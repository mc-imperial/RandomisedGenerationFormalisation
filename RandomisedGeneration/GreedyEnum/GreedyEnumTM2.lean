import Mathlib
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-- The stacks used by the greedy gen TM2 machine.

    Stack layout at quiescent points (start of each round):

    ── Main stacks ──
    • target:  [t₀, t₁, ..., tₖ]  — the word to recognise, first symbol on top.
               Unchanged throughout execution.
    • counter: [b₀, b₁, ..., bₘ]  — binary representation of the next input number
               to spawn (LSB on top, no leading falses). [] represents 0.
    • input:   [b₁, b₂, ...]  — the remaining unread input bits.
               Bits are the binary digits of the instance's input number;
               consumed bits have been popped.
    • workL:   [w₁, w₂, ...]  — the work tape cells to the left of the head
               (closest to head first).
    • workR:   Same structure as workL but for cells to the right of the head.
    • output:  [o₁, o₂, ...]  — the output symbols produced so far (most recent on top).

    ── Save stacks ──
    Mirror the corresponding main stacks. Used during the check phase and step phase
    to temporarily hold instance data while iterating through instances.
    Empty at quiescent points. -/
inductive GreedyEnumStack : Type u
  | target
  | counter
  | input
  | workL
  | workR
  | output
  | saveTarget
  | saveCounter

deriving instance DecidableEq for GreedyEnumStack
deriving instance Fintype for GreedyEnumStack
deriving instance Inhabited for GreedyEnumStack

/-- The type of elements stored on each stack. --/
def stackAlphabet (Γw Γo Q : Type u)
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    GreedyEnumStack → Type u
  | GreedyEnumStack.target      => Γo
  | GreedyEnumStack.counter     => ULift.{u} Bool
  | GreedyEnumStack.input       => ULift.{u} Bool
  | GreedyEnumStack.workL       => Γw
  | GreedyEnumStack.workR       => Γw
  | GreedyEnumStack.output      => Γo
  | GreedyEnumStack.saveTarget  => Γo
  | GreedyEnumStack.saveCounter => ULift.{u} Bool

-- Labels for the greedy gen TM2 machine, corresponding to subroutine entry points.
inductive GreedyEnumLabel : Type u
  -- Setup
  | copyCounter                     -- pop counter bits to saveCounter
  | copyCounter_restore             -- restore counter + push bits to input
  | initRun                         -- set transQ := gen.init, transW := gen.blank
  -- Run loop
  | runStep                         -- pop input, peek workR, applyDelta, branch
  | runStep_apply                   -- update workR/workL per direction, push output
  | runStep_moveHead
  -- Check output
  | checkOutput                     -- pop output + pop target, compare
  | checkOutput_restoreTarget       -- restore target from saveTarget after mismatch/match
  -- Teardown
  | clearInput                      -- pop all remaining input bits
  | clearWorkL                      -- pop all workL
  | clearWorkR                      -- pop all workR
  | clearOutput                     -- pop all output
  -- Counter
  | counter_increment
  | counter_increment_loop
  | counter_increment_restore
deriving DecidableEq, Fintype

set_option linter.style.whitespace false
set_option linter.style.longLine false
structure GreedyEnumSigma (Γw Γo Q : Type u)
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] where
  transQ      : Option Q
  transW      : Γw
  transWDir   : WorkTapeDirection
  transOut    : Option Γo
  transHalted : Bool
  inputBit    : Bool
  carry       : Option Bool
  peekBit     : Option Bool       -- counter increment scratch
  peekTarget  : Option Γo         -- for output comparison
  peekOut     : Option Γo         -- for output comparison
set_option linter.style.whitespace true
set_option linter.style.longLine true

instance : Inhabited GreedyEnumLabel := ⟨GreedyEnumLabel.copyCounter⟩

instance : Inhabited (GreedyEnumSigma Γw Γo Q) :=
  ⟨{ transQ      := none
     transW      := default
     transWDir   := WorkTapeDirection.N
     transOut    := none
     transHalted := false
     inputBit    := false
     carry       := none
     peekBit     := none
     peekTarget  := none
     peekOut     := none }⟩

instance : Fintype (ULift.{u} Bool) :=
  Fintype.ofEquiv Bool ⟨ULift.up, ULift.down, fun _ => rfl, fun _ => rfl⟩

instance : DecidableEq (ULift.{u} Bool) :=
  fun a b => decidable_of_iff (a.down = b.down) (by cases a; cases b; simp [ULift.ext_iff])

instance [Fintype Γw] [Fintype Γo] [Fintype Q] [DecidableEq Γw] [DecidableEq Γo] [DecidableEq Q] :
    Fintype (GreedyEnumSigma Γw Γo Q) :=
  Fintype.ofEquiv
    (Option Q × Γw × WorkTapeDirection × Option Γo × Bool × Bool ×
     Option Bool × Option Bool × Option Γo × Option Γo)
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j⟩ =>
        { transQ := a, transW := b, transWDir := c, transOut := d,
          transHalted := e, inputBit := f, carry := g,
          peekBit := h, peekTarget := i, peekOut := j }
      invFun := fun σ =>
        (σ.transQ, σ.transW, σ.transWDir, σ.transOut,
         σ.transHalted, σ.inputBit, σ.carry,
         σ.peekBit, σ.peekTarget, σ.peekOut)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def greedyEnumInit (target : List Γo) :
    Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.init GreedyEnumStack.target target

/-- Apply the generator's transition function to the current instance.
    Reads transQ (current state), inputBit (current input), and transW (head symbol).
    On halt (δ returns none): sets transHalted := true, direction to N, no output.
    On step (δ returns some): updates transQ, transW, transOut, transWDir,
    transHalted := false. The input direction is ignored (greedy always advances). -/
def applyDelta
    (gen : Generator Γw Γo Q)
    (σ : GreedyEnumSigma Γw Γo Q) : GreedyEnumSigma Γw Γo Q :=
    match gen.δ (σ.transQ.getD gen.init) σ.inputBit σ.transW with
    | none =>
        { σ with
          transWDir   := WorkTapeDirection.N
          transOut    := none
          transHalted := true }
    | some (q', w', o, _, wd) =>
        { σ with
          transQ      := some q'
          transW      := w'
          transOut    := o
          transWDir   := wd
          transHalted := false }

/-
══════════════════════════════════════════════════════════════════════════════
  Greedy Enumeration TM2 — Procedures
══════════════════════════════════════════════════════════════════════════════

  Single-instance greedy enumeration. For each bitstring (enumerated by a
  binary counter), run the generator for len steps (one bit per step since
  greedy), check output on halt, then advance to the next bitstring.

  Stacks (no separators — single instance at a time):
    target : Γo, counter : ULift Bool, input : ULift Bool,
    workL : Γw, workR : Γw, output : Γo,
    saveTarget : Γo, saveCounter : ULift Bool

  Convention: workR top = head cell under the read/write head.
              workL top = cell immediately to the left of head.

  Register file (GreedyEnumSigma):
    transQ, transW, transWDir, transOut, transHalted — from applyDelta
    inputBit    — current input bit
    carry       — counter increment scratch
    peekBit     — scratch: peeked bit / boolean flag
    peekTarget  — peeked target symbol (for output comparison)
    peekOut     — peeked output symbol (for output comparison)
══════════════════════════════════════════════════════════════════════════════
-/

-- Labels (add runStep_moveHead to the existing enum)
-- Assumed labels:
--   copyCounter, copyCounter_restore, initRun,
--   runStep, runStep_apply, runStep_moveHead,
--   checkOutput, checkOutput_restoreTarget,
--   clearWorkL, clearWorkR, clearOutput,
--   counter_increment, counter_increment_loop, counter_increment_restore

/-
══════════════════════════════════════════════════════════════════════════════
  Setup: Copy counter → input, initialise generator
══════════════════════════════════════════════════════════════════════════════
-/

/-- Pop all counter bits to saveCounter. -/
def copyCounter :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.counter (fun σ b =>
    { σ with peekBit := b.map ULift.down })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.copyCounter_restore) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.counter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push GreedyEnumStack.saveCounter
          (fun σ => ULift.up (σ.peekBit.getD false))
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.copyCounter) )

/-- Pop saveCounter back to counter AND input simultaneously. -/
def copyCounter_restore :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.saveCounter (fun σ b =>
    { σ with peekBit := b.map ULift.down })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.initRun) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.saveCounter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push GreedyEnumStack.counter
          (fun σ => ULift.up (σ.peekBit.getD false))
      <| Turing.TM2.Stmt.push GreedyEnumStack.input
          (fun σ => ULift.up (σ.peekBit.getD false))
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.copyCounter_restore) )

/-- Set transQ := gen.init, transW := gen.blank, enter step loop. -/
def initRun (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.load (fun σ =>
    { σ with transQ := some gen.init, transW := gen.blank })
  <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep)

/-
══════════════════════════════════════════════════════════════════════════════
  Run loop
══════════════════════════════════════════════════════════════════════════════
-/

/-- Main step loop. Peek input:
    • Empty → steps exhausted, teardown.
    • Non-empty → pop bit, peek/pop workR head, apply delta, branch. -/
def runStep (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  -- Peek input
  Turing.TM2.Stmt.peek GreedyEnumStack.input (fun σ b => { σ with
    inputBit := match b with | some b => b.down | none => false
    -- Stash "had input" in peekBit: some true = had bit, some false = empty
    peekBit  := some b.isSome })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some false)
    ( -- Input empty → teardown (clear remaining stacks)
      Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearWorkL) )
    ( -- Pop the input bit (greedy: always consume one bit per step)
      Turing.TM2.Stmt.pop GreedyEnumStack.input (fun σ _ => σ)
      -- Peek workR to get head symbol, set transW
      <| Turing.TM2.Stmt.peek GreedyEnumStack.workR (fun σ w => { σ with
          transW := w.getD gen.blank
          -- Stash "workR had data" in peekBit
          peekBit := some w.isSome })
      -- If workR had a symbol, pop it (will be replaced by applyDelta result)
      <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some true)
        ( Turing.TM2.Stmt.pop GreedyEnumStack.workR (fun σ _ => σ)
          <| Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
          <| Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
            ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.checkOutput) )
            ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep_apply) ) )
        ( -- workR was empty, transW = gen.blank, no need to pop
          Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
          <| Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
            ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.checkOutput) )
            ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep_apply) ) ) )

/-- Apply transition: push new head to workR, optionally emit output,
    then move work tape head. -/
def runStep_apply :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  -- Push new head symbol (transW as set by applyDelta)
  Turing.TM2.Stmt.push GreedyEnumStack.workR (fun σ => σ.transW)
  -- Emit output if present
  <| Turing.TM2.Stmt.branch (fun σ => σ.transOut.isSome)
    ( Turing.TM2.Stmt.push GreedyEnumStack.output
        (fun σ => σ.transOut.getD default)
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep_moveHead) )
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep_moveHead) )

/-- Move work tape head according to transWDir, then loop to runStep.

    After runStep_apply, workR = [transW, old_r1, old_r2, ...].
    workL is unchanged from before the step.

    Move N: no change. Head stays at workR top = transW.
    Move L: new head = workL top (or blank if empty).
            Pop workL, push onto workR. workR = [l1, transW, r1, ...].
    Move R: transW moves to the left of the new head.
            Pop workR (= transW), push to workL.
            If workR now empty, push gen.blank (new head on blank cell). -/
def runStep_moveHead (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch
    (fun σ => match σ.transWDir with | WorkTapeDirection.L => true | _ => false)
    ( -- Move L: pop workL → push to workR (becomes new head)
      Turing.TM2.Stmt.peek GreedyEnumStack.workL (fun σ w => { σ with
        transW := w.getD gen.blank  -- reuse transW as temp for the popped cell
        peekBit := some w.isSome })
      <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some true)
        ( Turing.TM2.Stmt.pop GreedyEnumStack.workL (fun σ _ => σ)
          <| Turing.TM2.Stmt.push GreedyEnumStack.workR (fun σ => σ.transW)
          <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep) )
        ( -- workL empty: push blank as new head
          Turing.TM2.Stmt.push GreedyEnumStack.workR (fun _ => gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep) ) )
    ( Turing.TM2.Stmt.branch
      (fun σ => match σ.transWDir with | WorkTapeDirection.R => true | _ => false)
      ( -- Move R: pop workR (= transW, the cell we just wrote), push to workL.
        -- Next workR top becomes new head. If workR empty after pop, push blank.
        Turing.TM2.Stmt.pop GreedyEnumStack.workR (fun σ w => { σ with transW := w.getD gen.blank })
        <| Turing.TM2.Stmt.push GreedyEnumStack.workL (fun σ => σ.transW)
        <| Turing.TM2.Stmt.peek GreedyEnumStack.workR (fun σ w => { σ with
            peekBit := some w.isSome })
        <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some false)
          ( -- workR empty after pop: push blank as new head
            Turing.TM2.Stmt.push GreedyEnumStack.workR (fun _ => gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep) )
          ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep) ) )
      ( -- Move N: no movement
        Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.runStep) ) )

/-
══════════════════════════════════════════════════════════════════════════════
  Check output: compare output stack against target
══════════════════════════════════════════════════════════════════════════════

  Both stacks have first symbol on top. The output stack has symbols in
  emission order (most recent on top), while the target has first symbol
  on top. For a greedy generator that always appends to output, the output
  stack in reverse is the produced word. The target is stored first-on-top.

  We compare element by element, consuming both. Consumed target elements
  are saved to saveTarget for restoration on mismatch.

  Match (both exhausted simultaneously): halt (accept).
  Mismatch or length difference: restore target, go to teardown.
-/

/-- Compare output vs target element by element. -/
def checkOutput :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  -- Peek both stacks
  Turing.TM2.Stmt.peek GreedyEnumStack.target (fun σ t =>
    { σ with peekTarget := t })
  <| Turing.TM2.Stmt.peek GreedyEnumStack.output (fun σ o =>
    { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone && σ.peekOut.isNone)
    ( -- Both exhausted: match! Halt.
      Turing.TM2.Stmt.halt )
    ( Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone || σ.peekOut.isNone)
      ( -- One exhausted but not both: length mismatch → restore target
        Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.checkOutput_restoreTarget) )
      ( -- Both have elements: compare
        Turing.TM2.Stmt.branch (fun σ => match σ.peekTarget, σ.peekOut with
            | some t, some o => decide (t = o)
            | _, _ => false)
          ( -- Match: pop both, save target element, continue comparing
            Turing.TM2.Stmt.pop GreedyEnumStack.target (fun σ _ => σ)
            <| Turing.TM2.Stmt.pop GreedyEnumStack.output (fun σ _ => σ)
            <| Turing.TM2.Stmt.push GreedyEnumStack.saveTarget
                (fun σ => σ.peekTarget.getD default)
            <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.checkOutput) )
          ( -- Mismatch: restore target
            Turing.TM2.Stmt.goto
              (fun _ => GreedyEnumLabel.checkOutput_restoreTarget) ) ) )

/-- Restore target from saveTarget, then proceed to teardown.
    Also restores any remaining output symbols we popped
    (but since we're about to clear output anyway, we skip that). -/
def checkOutput_restoreTarget :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.saveTarget (fun σ t =>
    { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( -- All restored → teardown
      Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearInput) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.saveTarget (fun σ _ => σ)
      <| Turing.TM2.Stmt.push GreedyEnumStack.target
          (fun σ => σ.peekTarget.getD default)
      <| Turing.TM2.Stmt.goto
          (fun _ => GreedyEnumLabel.checkOutput_restoreTarget) )

/-
══════════════════════════════════════════════════════════════════════════════
  Teardown: clear instance stacks, increment counter, loop
══════════════════════════════════════════════════════════════════════════════
-/

/-- Clear remaining input bits (may already be empty). -/
def clearInput :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.input (fun σ b =>
    { σ with peekBit := b.map ULift.down })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearWorkL) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearInput) )

/-- Clear workL stack. -/
def clearWorkL :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.workL (fun σ w =>
    { σ with peekBit := some w.isSome })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some false)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearWorkR) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearWorkL) )

/-- Clear workR stack. -/
def clearWorkR :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.workR (fun σ w =>
    { σ with peekBit := some w.isSome })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit == some false)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearOutput) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearWorkR) )

/-- Clear output stack. -/
def clearOutput :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.output (fun σ o =>
    { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.counter_increment) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.clearOutput) )

/-
══════════════════════════════════════════════════════════════════════════════
  Counter increment (adapted from old dovetailing code)
══════════════════════════════════════════════════════════════════════════════

  Binary increment with carry. Counter stores LSB on top, no leading falses.
  After increment, goes to copyCounter to start the next bitstring.
-/

/-- Set carry := true, enter increment loop. -/
def counter_increment :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.load (fun σ => { σ with carry := some true })
  <| Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.counter_increment_loop)

/-- Process one counter bit: XOR with carry for new bit, AND for new carry.
    Pop from counter, push result to saveCounter. -/
def counter_increment_loop :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.counter (fun σ b =>
    { σ with peekBit := b.map ULift.down })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( -- Counter empty: if carry set, push 1; then restore
      Turing.TM2.Stmt.branch (fun σ => σ.carry.getD false)
        ( Turing.TM2.Stmt.push GreedyEnumStack.saveCounter
            (fun _ => ULift.up true)
          <| Turing.TM2.Stmt.goto
              (fun _ => GreedyEnumLabel.counter_increment_restore) )
        ( Turing.TM2.Stmt.goto
            (fun _ => GreedyEnumLabel.counter_increment_restore) ) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.counter (fun σ _ => σ)
      <| Turing.TM2.Stmt.load (fun σ =>
          let bit      := σ.peekBit.getD false
          let carry    := σ.carry.getD false
          let newBit   := Bool.xor bit carry
          let newCarry := bit && carry
          { σ with peekBit := some newBit, carry := some newCarry })
      <| Turing.TM2.Stmt.push GreedyEnumStack.saveCounter
          (fun σ => ULift.up (σ.peekBit.getD false))
      <| Turing.TM2.Stmt.goto
          (fun _ => GreedyEnumLabel.counter_increment_loop) )

/-- Restore counter from saveCounter, then start next round. -/
def counter_increment_restore :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek GreedyEnumStack.saveCounter (fun σ b =>
    { σ with peekBit := b.map ULift.down })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( -- Done restoring → start next bitstring
      Turing.TM2.Stmt.goto (fun _ => GreedyEnumLabel.copyCounter) )
    ( Turing.TM2.Stmt.pop GreedyEnumStack.saveCounter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push GreedyEnumStack.counter
          (fun σ => ULift.up (σ.peekBit.getD false))
      <| Turing.TM2.Stmt.goto
          (fun _ => GreedyEnumLabel.counter_increment_restore) )

/-
══════════════════════════════════════════════════════════════════════════════
  Machine definition
══════════════════════════════════════════════════════════════════════════════
-/

def greedyEnumMachine (gen : Generator Γw Γo Q) :
    GreedyEnumLabel →
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q)
  | GreedyEnumLabel.copyCounter              => copyCounter
  | GreedyEnumLabel.copyCounter_restore      => copyCounter_restore
  | GreedyEnumLabel.initRun                  => initRun gen
  | GreedyEnumLabel.runStep                  => runStep gen
  | GreedyEnumLabel.runStep_apply            => runStep_apply
  | GreedyEnumLabel.runStep_moveHead         => runStep_moveHead gen
  | GreedyEnumLabel.checkOutput              => checkOutput
  | GreedyEnumLabel.checkOutput_restoreTarget => checkOutput_restoreTarget
  | GreedyEnumLabel.clearInput               => clearInput
  | GreedyEnumLabel.clearWorkL               => clearWorkL
  | GreedyEnumLabel.clearWorkR               => clearWorkR
  | GreedyEnumLabel.clearOutput              => clearOutput
  | GreedyEnumLabel.counter_increment        => counter_increment
  | GreedyEnumLabel.counter_increment_loop   => counter_increment_loop
  | GreedyEnumLabel.counter_increment_restore => counter_increment_restore

end GreedyEnum

end RandomisedGeneration
