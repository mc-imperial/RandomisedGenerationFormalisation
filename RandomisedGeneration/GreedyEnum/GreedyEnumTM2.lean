import Mathlib
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]
set_option linter.unusedSectionVars false

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

-- The type of elements stored on each stack.
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
  Turing.TM2.init GreedyEnumStack.target target.reverse

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

abbrev GECfg (Γw Γo Q : Type u) [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :=
  Turing.TM2.Cfg.{u,u,u,u}
    (stackAlphabet Γw Γo Q)
    GreedyEnumLabel.{u}
    (GreedyEnumSigma Γw Γo Q)

abbrev GEStep (gen : Generator Γw Γo Q) : GECfg Γw Γo Q → Option (GECfg Γw Γo Q) :=
  Turing.TM2.step (greedyEnumMachine gen)

abbrev GEEval (gen : Generator Γw Γo Q) (target : List Γo) : Part (List Γo) :=
  @Turing.TM2.eval.{u,u,u,u} GreedyEnumStack (stackAlphabet Γw Γo Q)
    GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) _ _ _
    (greedyEnumMachine gen) GreedyEnumStack.target target

def TM2Reaches (gen : Generator Γw Γo Q) (cfg cfg' : GECfg Γw Γo Q) : Prop :=
  Relation.ReflTransGen (fun a b => GEStep gen a = some b) cfg cfg'

def TM2Halts (gen : Generator Γw Γo Q) (cfg : GECfg Γw Γo Q) : Prop :=
  ∃ cfg', TM2Reaches gen cfg cfg' ∧ GEStep gen cfg' = none

lemma TM2Reaches_trans {gen : Generator Γw Γo Q}
    {cfg₁ cfg₂ cfg₃ : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
      GreedyEnumLabel (GreedyEnumSigma Γw Γo Q)}
    (h₁ : TM2Reaches gen cfg₁ cfg₂) (h₂ : TM2Reaches gen cfg₂ cfg₃) :
    TM2Reaches gen cfg₁ cfg₃ :=
  Relation.ReflTransGen.trans h₁ h₂

def WorkTapeMatches
    (gen : Generator Γw Γo Q)
    (work : ℤ → Γw)
    (workIndex : ℤ)
    (workL workR : List Γw) : Prop :=
  (∀ i : ℕ, (h : i < workR.length) →
    workR.get ⟨i, h⟩ = work (workIndex + i)) ∧
  (∀ i : ℕ, i ≥ workR.length →
    work (workIndex + i) = gen.blank) ∧
  (∀ i : ℕ, (h : i < workL.length) →
    workL.get ⟨i, h⟩ = work (workIndex - (↑i + 1))) ∧
  (∀ i : ℕ, i ≥ workL.length →
    work (workIndex - (↑i + 1)) = gen.blank)

structure CopyCounterInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []

structure CopyCounterRestoreInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = counter.reverse
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

structure InitRunInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.initRun
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

structure RunStepInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop gcfg.inputIndex
  h_transQ      : cfg.var.transQ = some gcfg.state
  h_work        : WorkTapeMatches gen gcfg.work gcfg.workIndex
                    (cfg.stk GreedyEnumStack.workL) (cfg.stk GreedyEnumStack.workR)
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg.output.reverse

structure RunStepApplyInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (q' : Q) (w' : Γw) (o : Option Γo) (wd : WorkTapeDirection)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep_apply
  h_delta       : gen.δ gcfg.state
                    (gcfg.input gcfg.inputIndex)
                    (gcfg.work gcfg.workIndex)
                  = some (q', w', o, InputTapeDirection.R, wd)
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop (gcfg.inputIndex + 1)
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg.output.reverse
  h_workL       : ∀ i : ℕ, (h : i < (cfg.stk GreedyEnumStack.workL).length) →
                    (cfg.stk GreedyEnumStack.workL).get ⟨i, h⟩ =
                      gcfg.work (gcfg.workIndex - (↑i + 1))
  h_workL_blank : ∀ i : ℕ, i ≥ (cfg.stk GreedyEnumStack.workL).length →
                    gcfg.work (gcfg.workIndex - (↑i + 1)) = gen.blank
  h_workR       : ∀ i : ℕ, (h : i < (cfg.stk GreedyEnumStack.workR).length) →
                    (cfg.stk GreedyEnumStack.workR).get ⟨i, h⟩ =
                      gcfg.work (gcfg.workIndex + (↑i + 1))
  h_workR_blank : ∀ i : ℕ, i ≥ (cfg.stk GreedyEnumStack.workR).length →
                    gcfg.work (gcfg.workIndex + (↑i + 1)) = gen.blank
  h_transQ      : cfg.var.transQ      = some q'
  h_transW      : cfg.var.transW      = w'
  h_transOut    : cfg.var.transOut     = o
  h_transWDir   : cfg.var.transWDir   = wd
  h_transHalted : cfg.var.transHalted = false

structure RunStepMoveHeadInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg gcfg' : GenConfig Γw Γo Q)
    (wd : WorkTapeDirection)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep_moveHead
  h_gen_step    : step gen gcfg = some gcfg'
  h_wd          : gcfg'.workIndex = gcfg.workIndex + (wd : ℤ)
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop gcfg'.inputIndex
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg'.output.reverse
  h_work        : WorkTapeMatches gen gcfg'.work gcfg.workIndex
                    (cfg.stk GreedyEnumStack.workL) (cfg.stk GreedyEnumStack.workR)
  h_transWDir   : cfg.var.transWDir = wd

/-- When input is exhausted and the generator halts, runStep branches
    to checkOutput. -/
structure CheckOutputInvariant
    (stackTarget cmpTarget : List Γo)
    (remaining_target : List Γo)
    (remaining_output : List Γo)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.checkOutput
  h_target      : cfg.stk GreedyEnumStack.target      = remaining_target
  h_output      : cfg.stk GreedyEnumStack.output      = remaining_output
  -- saveTarget holds the already-compared prefix (reversed)
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget   =
      (stackTarget.take (stackTarget.length - remaining_target.length)).reverse
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []

structure ClearInputInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.clearInput
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_output      : cfg.stk GreedyEnumStack.output      = []

structure CounterIncrementInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []

def counterToInput (counter : List (ULift.{u} Bool)) : ℕ → Bool :=
  fun i => match counter[i]? with
    | some b => b.down
    | none   => false

def counterIncrement : List (ULift.{u} Bool) → List (ULift.{u} Bool)
  | [] => [ULift.up true]
  | ⟨false⟩ :: rest => ⟨true⟩ :: rest
  | ⟨true⟩ :: rest => ⟨false⟩ :: counterIncrement rest

section CopyCounterPhase

private structure CopyCounterLoopInvariant
    (target : List Γo)
    (remaining : List (ULift.{u} Bool))
    (saved : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = remaining
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = saved
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private structure CopyCounterRestoreLoopInvariant
    (target : List Γo)
    (restored : List (ULift.{u} Bool))
    (remaining : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = restored
  h_input       : cfg.stk GreedyEnumStack.input       = restored
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = remaining
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private lemma copyCounter_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (remaining saved : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterLoopInvariant target remaining saved cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterRestoreLoopInvariant target [] (remaining.reverse ++ saved) cfg' := by
  induction remaining generalizing saved cfg with
  | nil =>
    simp only [List.reverse_nil, List.nil_append]
    refine ⟨⟨some GreedyEnumLabel.copyCounter_restore,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hc : S GreedyEnumStack.counter = [] := hinv.h_counter
        simp only [Turing.TM2.step, greedyEnumMachine,
                   copyCounter, Turing.TM2.stepAux, hc, List.head?,
                   Option.map, Option.isNone, cond_true]
    · exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
             hinv.h_saveCounter, hinv.h_workL, hinv.h_workR,
             hinv.h_output, hinv.h_saveTarget⟩
  | cons b rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        CopyCounterLoopInvariant target rest (b :: saved) cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.copyCounter,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.counter => rest
                 | GreedyEnumStack.saveCounter => b :: saved
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hc : S GreedyEnumStack.counter = b :: rest := hinv.h_counter
          have hsc : S GreedyEnumStack.saveCounter = saved := hinv.h_saveCounter
          simp only [Turing.TM2.step, greedyEnumMachine,
                     copyCounter, Turing.TM2.stepAux, hc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons, Option.getD_some,
              ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hsc]
      · exact ⟨rfl, hinv.h_target, rfl, rfl, hinv.h_input,
               hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₁, hr₁, hinv₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, hinv₂⟩ := ih (b :: saved) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
    convert hinv₂ using 1
    simp [List.reverse_cons, List.append_assoc]

private lemma copyCounter_restore_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (restored remaining : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterRestoreLoopInvariant target restored remaining cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      InitRunInvariant target (remaining.reverse ++ restored) cfg' := by
  induction remaining generalizing restored cfg with
  | nil =>
    simp only [List.reverse_nil, List.nil_append]
    refine ⟨⟨some GreedyEnumLabel.initRun,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        have hl := hinv.h_label; simp only at hl; subst hl
        have hsc : S GreedyEnumStack.saveCounter = [] := hinv.h_saveCounter
        simp only [Turing.TM2.step, greedyEnumMachine,
                   copyCounter_restore, Turing.TM2.stepAux, hsc,
                   List.head?, Option.map, Option.isNone, cond_true]
    · exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
             hinv.h_saveCounter, hinv.h_workL, hinv.h_workR,
             hinv.h_output, hinv.h_saveTarget⟩
  | cons b rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        CopyCounterRestoreLoopInvariant target (b :: restored) rest cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.copyCounter_restore,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.counter => b :: restored
                 | GreedyEnumStack.input => b :: restored
                 | GreedyEnumStack.saveCounter => rest
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hsc : S GreedyEnumStack.saveCounter = b :: rest := hinv.h_saveCounter
          have hc : S GreedyEnumStack.counter = restored := hinv.h_counter
          have hi : S GreedyEnumStack.input = restored := hinv.h_input
          simp only [Turing.TM2.step, greedyEnumMachine,
                     copyCounter_restore, Turing.TM2.stepAux, hsc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons, Option.getD_some,
              ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hc, hi]
      · exact ⟨rfl, hinv.h_target, rfl, rfl, rfl,
               hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₁, hr₁, hinv₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, hinv₂⟩ := ih (b :: restored) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
    convert hinv₂ using 1
    simp [List.reverse_cons, List.append_assoc]

end CopyCounterPhase





section RunPhase

/-- After initRun loads the generator state, we're at runStep with
    the initial GenConfig. -/
private lemma initRun_to_runStep
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : InitRunInvariant stackTarget counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter
        (initConfig gen (counterToInput counter)) cfg' := by
  sorry
  -- One TM2 step: load sets transQ := some gen.init, transW := gen.blank,
  -- then goto runStep. Need to show the initial GenConfig matches.

/-- One iteration of the run loop: if input is non-empty and delta doesn't halt,
    we advance the GenConfig by one step and return to runStep. -/
private lemma runStep_step
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg gcfg' : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hInput : gcfg.inputIndex < counter.length)
    (hStep : step gen gcfg = some gcfg') :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter gcfg' cfg' := by
  sorry
  -- This is the big one. Path: runStep → runStep_apply → runStep_moveHead → runStep.
  -- Needs to go through the branch on input non-empty, pop input, peek workR,
  -- apply delta (non-halting), push new workR, emit output, move head.
  -- You may want to split this into sub-lemmas:
  --   runStep_to_apply, runStep_apply_to_moveHead, runStep_moveHead_to_runStep

/-- Run the full loop for N steps, chaining runStep_step. -/
private lemma runStep_loop
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (n : ℕ)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hSteps : ∀ i, i < n → gcfg.inputIndex + i < counter.length)
    (hAlive : ∀ i, i < n → ¬IsHalting gen (stepNHalt gen gcfg i)) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter (stepNHalt gen gcfg n) cfg' := by
  sorry
  -- Induction on n, using runStep_step at each iteration.

end RunPhase


section CheckOutputPhase

/-- When the run loop ends (input exhausted), we reach checkOutput
    or clearInput depending on whether the generator halted.
    This handles the halting case. -/
private lemma runStep_exhausted_halted_to_checkOutput
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hExhausted : gcfg.inputIndex = counter.length)
    (hHalted : IsHalting gen gcfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget gcfg.output.reverse
        stackTarget gcfg.output.reverse cfg' := by
  sorry
  -- runStep peeks input (empty), branches to checkOutput.
  -- Actually wait — looking at your runStep code, input empty → goto clearWorkL,
  -- not checkOutput. checkOutput is reached when delta returns halt (transHalted = true).
  -- Need to re-examine the flow here.

/-- When the run loop ends because delta halted (not input exhausted),
    we reach checkOutput. -/
private lemma runStep_halted_to_checkOutput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hInput : gcfg.inputIndex < counter.length)
    (hHalted : gen.δ gcfg.state (gcfg.input gcfg.inputIndex) (gcfg.work gcfg.workIndex) = none) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget gcfg.output.reverse
        stackTarget gcfg.output.reverse cfg' := by
  sorry
  -- runStep peeks input (non-empty), pops, peeks workR, applies delta,
  -- delta returns none → transHalted = true → goto checkOutput.

/-- One iteration of checkOutput: both have elements and they match. -/
private lemma checkOutput_step_match
    (gen : Generator Γw Γo Q)
    (stackTarget cmpTarget : List Γo)
    (t : Γo) (rest_t rest_o : List Γo)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CheckOutputInvariant stackTarget cmpTarget (t :: rest_t) (t :: rest_o) cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget cmpTarget rest_t rest_o cfg' := by
  sorry
  -- Peek target (some t), peek output (some t), not both none,
  -- not one none, compare equal → pop both, push target to saveTarget, goto checkOutput.

/-- checkOutput with both stacks empty → halt. -/
private lemma checkOutput_both_empty_halts
    (gen : Generator Γw Γo Q)
    (stackTarget cmpTarget : List Γo)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CheckOutputInvariant stackTarget cmpTarget [] [] cfg) :
    TM2Halts gen cfg := by
  sorry
  -- Peek target (none), peek output (none), both none → halt.
  -- One step to halted config. TM2Halts needs a cfg' with step = none.

/-- Chain checkOutput over matching lists. -/
private lemma checkOutput_matching_lists_halt
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (matched : List Γo)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CheckOutputInvariant stackTarget matched matched matched cfg) :
    TM2Halts gen cfg := by
  sorry
  -- Induction on matched, using checkOutput_step_match then checkOutput_both_empty_halts.

end CheckOutputPhase


section NoMatchPhase

/-- checkOutput with a mismatch → goto checkOutput_restoreTarget. -/
private lemma checkOutput_mismatch_to_restore
    (gen : Generator Γw Γo Q)
    (stackTarget cmpTarget : List Γo)
    (remaining_target remaining_output : List Γo)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CheckOutputInvariant stackTarget cmpTarget remaining_target remaining_output cfg)
    (hMismatch : remaining_target ≠ [] ∨ remaining_output ≠ [])
    -- Plus: they don't match at the head
    :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.checkOutput_restoreTarget ∧
      -- target is partially consumed, saveTarget has the consumed prefix
      True := by
  sorry

/-- Restore target from saveTarget, then reach clearInput. -/
private lemma checkOutput_restoreTarget_to_clearInput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (h_label : cfg.l = some GreedyEnumLabel.checkOutput_restoreTarget)
    -- ... stack conditions: target partially consumed, saveTarget has prefix ...
    :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      ClearInputInvariant stackTarget counter cfg' := by
  sorry
  -- Loop: pop saveTarget, push to target, until saveTarget empty.
  -- Then goto clearInput.

/-- When input is exhausted and generator did NOT halt,
    runStep goes to clearWorkL (via the "input empty" branch).
    This eventually reaches clearInput → counterIncrement. -/
private lemma runStep_exhausted_not_halted_to_clearInput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hExhausted : gcfg.inputIndex = counter.length) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      ClearInputInvariant stackTarget counter cfg' := by
  sorry
  -- runStep peeks input (empty) → goto clearWorkL.
  -- But ClearInputInvariant expects label = clearInput...
  -- Actually looking at your runStep code: input empty → goto clearWorkL, not clearInput.
  -- So this goes clearWorkL → clearWorkR → clearOutput → counter_increment.
  -- You might want to go directly to CounterIncrementInvariant here instead.

end NoMatchPhase












lemma copyCounter_to_initRun
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      InitRunInvariant target counter cfg' := by
  have hinv₀ : CopyCounterLoopInvariant target counter [] cfg :=
    ⟨hinv.h_label, hinv.h_target, hinv.h_counter, hinv.h_saveCounter,
     hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
  obtain ⟨cfg₁, hr₁, hinv₁⟩ := copyCounter_loop gen target counter [] cfg hinv₀
  simp only [List.append_nil] at hinv₁
  obtain ⟨cfg₂, hr₂, hinv₂⟩ := copyCounter_restore_loop gen target [] counter.reverse cfg₁ hinv₁
  refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
  simp only [List.reverse_reverse, List.append_nil] at hinv₂
  exact hinv₂

lemma initRun_no_match_to_copyCounter
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget cmpTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : InitRunInvariant stackTarget counter cfg)
    (hNoMatch : ¬(IsHalting gen
        (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length) ∧
      (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length).output
        = cmpTarget)) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant stackTarget (counterIncrement counter) cfg' := by
  -- 1. initRun_to_runStep
  -- 2. runStep_loop for counter.length steps
  -- 3. Two cases:
  --    a. Generator halted mid-run → runStep_halted_to_checkOutput
  --       → checkOutput mismatch → restore target → clearInput
  --       → counterIncrement → copyCounter
  --    b. Generator didn't halt, input exhausted
  --       → runStep_exhausted → clearInput → counterIncrement → copyCounter
  -- 4. Chain with clearInput_to_counterIncrement (you have this ✓)
  --    and counter_increment_to_copyCounter (you have this ✓)
  sorry

lemma initRun_match_halts
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget cmpTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : InitRunInvariant stackTarget counter cfg)
    (hHalt : IsHalting gen
        (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length))
    (hOut : (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length).output
        = cmpTarget) :
    TM2Halts gen cfg := by
  sorry

section CounterIncrement

private structure CounterIncrementLoopInvariant
    (target : List Γo)
    (remaining : List (ULift.{u} Bool))
    (processed : List (ULift.{u} Bool))
    (carry : Bool)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_loop
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = remaining
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = processed
  h_carry       : cfg.var.carry = some carry
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private structure CounterIncrementRestoreInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = counter.reverse
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

/-- Increment a bit list with carry (LSB first). -/
private def addCarry : List (ULift.{u} Bool) → Bool → List (ULift.{u} Bool)
  | [], false => []
  | [], true => [ULift.up true]
  | ⟨b⟩ :: rest, c =>
    ⟨Bool.xor b c⟩ :: addCarry rest (b && c)

-- Step 1: counter_increment → counter_increment_loop (one step)
private lemma counter_increment_to_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementLoopInvariant target counter [] true cfg' := by
  -- One TM2 step: load sets carry := some true, goto sets label
  refine ⟨⟨some GreedyEnumLabel.counter_increment_loop,
           { cfg.var with carry := some true },
           cfg.stk⟩, ?_, ?_⟩
  · -- Reachability: one step
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only
      have hl := hinv.h_label
      simp only at hl
      subst hl
      simp [greedyEnumMachine, counter_increment, Turing.TM2.stepAux]
  · -- The invariant holds
    exact ⟨rfl, hinv.h_target, hinv.h_counter, by exact hinv.h_saveCounter, rfl,
           hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩

-- Step 2: loop processes all bits
private lemma counter_increment_loop_to_restore
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (remaining processed : List (ULift.{u} Bool))
    (carry : Bool)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementLoopInvariant target remaining processed carry cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementRestoreInvariant target
        ((addCarry remaining carry).reverse ++ processed).reverse cfg' := by
  induction remaining generalizing processed carry cfg with
  | nil =>
    -- remaining = [], addCarry [] carry is either [] or [true]
    cases carry with
    | false =>
      -- addCarry [] false = [], so target counter = processed.reverse
      -- One step: peek counter (empty), branch isNone = true, branch carry = false, goto restore
      simp only [addCarry, List.reverse_nil, List.nil_append]
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
               { cfg.var with peekBit := none },
               cfg.stk⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hctr : S GreedyEnumStack.counter = [] := hinv.h_counter
          have hcarry := hinv.h_carry; simp only at hcarry
          simp only [Turing.TM2.step, greedyEnumMachine,
                     counter_increment_loop, Turing.TM2.stepAux]
          rw [hctr]
          simp [List.head?, Option.map, Option.isNone, cond_true, hcarry]
      · exact ⟨rfl, hinv.h_target, hinv.h_counter,
          by simp [List.reverse_reverse, hinv.h_saveCounter],
          hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    | true =>
      -- addCarry [] true = [ULift.up true], push true to saveCounter, goto restore
      simp only [addCarry, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
               { cfg.var with peekBit := none },
               fun k => match k with
                 | GreedyEnumStack.saveCounter => ULift.up true :: processed
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hctr : S GreedyEnumStack.counter = [] := hinv.h_counter
          have hcarry := hinv.h_carry; simp only at hcarry
          have hsc := hinv.h_saveCounter; simp only at hsc
          simp only [Turing.TM2.step, greedyEnumMachine,
                     counter_increment_loop, Turing.TM2.stepAux]
          rw [hctr]
          simp only [Option.isNone, Option.map, List.head?, hcarry, Option.getD_some, cond_true,
            Option.getD_none, Bool.and_true, Bool.bne_true, Bool.not_false, List.tail_nil, ne_eq,
            reduceCtorEq, not_false_eq_true, Function.update_of_ne, Option.some.injEq,
            Turing.TM2.Cfg.mk.injEq, true_and]
          ext k; cases k <;> simp [Function.update, hsc]
      · refine ⟨rfl, ?_, ?_, ?_,
                hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
        · simp [hinv.h_target]
        · simp [hinv.h_counter]
        · simp [List.reverse_cons]
  | cons b rest ih =>
    -- Pop b from counter, compute newBit = xor b.down carry, newCarry = b.down && carry
    -- Push newBit to saveCounter, goto loop with rest, (ULift.up newBit :: processed), newCarry
    cases b with
    | up bv =>
      -- One iteration reaches CounterIncrementLoopInvariant with updated state
      have hone : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
          CounterIncrementLoopInvariant target rest
            (⟨Bool.xor bv carry⟩ :: processed) (bv && carry) cfg₁ := by
        refine ⟨⟨some GreedyEnumLabel.counter_increment_loop,
                 { cfg.var with
                   peekBit := some (Bool.xor bv carry)
                   carry := some (bv && carry) },
                 fun k => match k with
                   | GreedyEnumStack.counter => rest
                   | GreedyEnumStack.saveCounter => ⟨Bool.xor bv carry⟩ :: processed
                   | other => cfg.stk other⟩, ?_, ?_⟩
        · apply Relation.ReflTransGen.single
          cases cfg with
          | mk l v S =>
            have hl := hinv.h_label; simp only at hl; subst hl
            have hctr : S GreedyEnumStack.counter = ⟨bv⟩ :: rest := hinv.h_counter
            have hcarry := hinv.h_carry; simp only at hcarry
            have hsc := hinv.h_saveCounter; simp only at hsc
            simp only [Turing.TM2.step, greedyEnumMachine,
                       counter_increment_loop, Turing.TM2.stepAux]
            rw [hctr]
            simp only [Option.isNone, Option.map, List.head?, hcarry, Option.getD_some,
              List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
              cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hsc]
        · exact ⟨rfl, hinv.h_target, rfl, rfl, rfl,
                 hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
      obtain ⟨cfg₁, hreach₁, hinv₁⟩ := hone
      obtain ⟨cfg₂, hreach₂, hinv₂⟩ :=
        ih (⟨Bool.xor bv carry⟩ :: processed) (bv && carry) cfg₁ hinv₁
      refine ⟨cfg₂, TM2Reaches_trans hreach₁ hreach₂, ?_⟩
      -- Need: addCarry (⟨bv⟩ :: rest) carry = ⟨Bool.xor bv carry⟩ :: addCarry rest (bv && carry)
      simp only [addCarry]
      convert hinv₂ using 1
      simp [List.reverse_append, List.reverse_cons, List.reverse_reverse,
            List.append_assoc]

-- Step 3: restore → copyCounter
private structure RestoreLoopInvariant
    (target : List Γo)
    (moved : List (ULift.{u} Bool))
    (rest : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = moved
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = rest
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private lemma restore_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (moved : List (ULift.{u} Bool))
    (rest : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RestoreLoopInvariant target moved rest cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target (rest.reverse ++ moved) cfg' := by
  induction rest generalizing moved cfg with
  | nil =>
    -- saveCounter empty: one step (peek, branch true, goto copyCounter)
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨some GreedyEnumLabel.copyCounter,
           { cfg.var with peekBit := none },
           cfg.stk⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        have hl := hinv.h_label
        simp only at hl
        subst hl
        simp only [Turing.TM2.step, greedyEnumMachine,
                    counter_increment_restore, Turing.TM2.stepAux]
        have hsc : S GreedyEnumStack.saveCounter = [] := hinv.h_saveCounter
        rw [hsc]
        simp [List.head?, Option.map, Option.isNone]
    · simp only [List.reverse_nil, List.nil_append]
      exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
            hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget, hinv.h_saveCounter⟩
  | cons b rest' ih =>
    -- After one loop iteration, we have RestoreLoopInvariant with (b :: moved) and rest'
    -- Then ih gives us the result
    -- First show one iteration
    obtain ⟨cfg₁, hreach₁, hinv₁⟩ : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        RestoreLoopInvariant target (b :: moved) rest' cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
                  { cfg.var with peekBit := some b.down },
                  fun k => match k with
                    | GreedyEnumStack.counter => b :: moved
                    | GreedyEnumStack.saveCounter => rest'
                    | other => cfg.stk other⟩, ?_, ?_⟩
      · -- One TM2 step
        apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hsc : S GreedyEnumStack.saveCounter = b :: rest' := hinv.h_saveCounter
          have hc : S GreedyEnumStack.counter = moved := hinv.h_counter
          simp only [Turing.TM2.step, greedyEnumMachine,
                    counter_increment_restore, Turing.TM2.stepAux]
          rw [hsc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons,
              Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
              cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k
            cases k <;> simp [Function.update, hc]
      · -- The invariant holds
        exact ⟨rfl, hinv.h_target, rfl, rfl,
              hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₂, hreach₂, hinv₂⟩ := ih (b :: moved) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hreach₁ hreach₂, ?_⟩
    -- rest'.reverse ++ (b :: moved) = (b :: rest').reverse ++ moved
    rwa [List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma counter_increment_restore_to_copyCounter
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementRestoreInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target counter cfg' := by
  have hinv' : RestoreLoopInvariant target [] counter.reverse cfg :=
    ⟨hinv.h_label, hinv.h_target, hinv.h_counter, hinv.h_saveCounter,
     hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
  obtain ⟨cfg', hreach, hcopy⟩ := restore_loop gen target [] counter.reverse cfg hinv'
  refine ⟨cfg', hreach, ?_⟩
  simp only [List.reverse_reverse, List.append_nil] at hcopy
  exact hcopy

private lemma addCarry_false (l : List (ULift.{u} Bool)) :
    addCarry l false = l := by
  induction l with
  | nil => simp [addCarry]
  | cons b rest ih =>
    cases b with
    | up b => cases b <;> simp [addCarry, Bool.xor, ih]

private lemma counterIncrement_eq_addCarry (counter : List (ULift.{u} Bool)) :
    counterIncrement counter = addCarry counter true := by
  induction counter with
  | nil => simp [counterIncrement, addCarry]
  | cons b rest ih =>
    cases b with
    | up b =>
      cases b <;> simp [counterIncrement, addCarry, Bool.xor, addCarry_false, *]

lemma counter_increment_to_copyCounter
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target (counterIncrement counter) cfg' := by
  -- Step 1: counter_increment → counter_increment_loop
  obtain ⟨cfg₁, hreach₁, hinv₁⟩ := counter_increment_to_loop gen target counter cfg hinv
  -- Step 2: loop processes all bits
  obtain ⟨cfg₂, hreach₂, hinv₂⟩ :=
    counter_increment_loop_to_restore gen target counter [] true cfg₁ hinv₁
  -- Simplify the counter expression in hinv₂
  simp only [List.append_nil, List.reverse_reverse] at hinv₂
  -- Step 3: restore → copyCounter
  obtain ⟨cfg₃, hreach₃, hinv₃⟩ :=
    counter_increment_restore_to_copyCounter gen target _ cfg₂ hinv₂
  -- Chain reachability and rewrite counter
  refine ⟨cfg₃, ?_, ?_⟩
  · exact TM2Reaches_trans (TM2Reaches_trans hreach₁ hreach₂) hreach₃
  · rwa [counterIncrement_eq_addCarry]

end CounterIncrement


section ClearPhase

private lemma clear_stack_input
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (input : List (ULift.{u} Bool))
    (workL : List Γw) (workR : List Γw)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (h_label : cfg.l = some GreedyEnumLabel.clearInput)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = input)
    (h_workL : cfg.stk GreedyEnumStack.workL = workL)
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = [])
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearWorkL ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = workL ∧
      cfg'.stk GreedyEnumStack.workR = workR ∧
      cfg'.stk GreedyEnumStack.output = [] ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction input generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearWorkL,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hi : S GreedyEnumStack.input = [] := h_input
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearInput, Turing.TM2.stepAux]
      rw [hi]
      simp [List.head?, Option.map, Option.isNone, cond_true]
  | cons b rest ih =>
    -- One step: peek input (non-empty), branch, pop, goto clearInput
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearInput ∧
        cfg₁.stk GreedyEnumStack.input = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.workL = workL ∧
        cfg₁.stk GreedyEnumStack.workR = workR ∧
        cfg₁.stk GreedyEnumStack.output = [] ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearInput,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.input => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_workL, h_workR,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hi : S GreedyEnumStack.input = b :: rest := h_input
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearInput, Turing.TM2.stepAux]
        rw [hi]
        cases b with
        | up bv =>
          simp only [Option.isNone, Option.map, List.head?, List.tail_cons,
            cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
          ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hi₁, ht₁, hc₁, hwl₁, hwr₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_workL
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (workL : List Γw) (workR : List Γw)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (h_label : cfg.l = some GreedyEnumLabel.clearWorkL)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = workL)
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = [])
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearWorkR ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = [] ∧
      cfg'.stk GreedyEnumStack.workR = workR ∧
      cfg'.stk GreedyEnumStack.output = [] ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction workL generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearWorkR,
             { cfg.var with peekBit := some false },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hwl : S GreedyEnumStack.workL = [] := h_workL
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearWorkL, Turing.TM2.stepAux]
      rw [hwl]
      simp [List.head?, Option.isSome, BEq.beq]
      rfl
  | cons w rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearWorkL ∧
        cfg₁.stk GreedyEnumStack.workL = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.input = [] ∧
        cfg₁.stk GreedyEnumStack.workR = workR ∧
        cfg₁.stk GreedyEnumStack.output = [] ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearWorkL,
               { cfg.var with peekBit := some true },
               fun k => match k with
                 | GreedyEnumStack.workL => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_input, h_workR,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hwl : S GreedyEnumStack.workL = w :: rest := h_workL
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearWorkL, Turing.TM2.stepAux]
        rw [hwl]
        simp only [Option.isSome, List.head?, Option.some_beq_some, beq_false,
          Bool.not_true, List.tail_cons, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        have : Option.instBEq.beq (some true) (some false) = false := by decide
        ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hwl₁, ht₁, hc₁, hi₁, hwr₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_workR
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (workR : List Γw)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (h_label : cfg.l = some GreedyEnumLabel.clearWorkR)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = [])
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = [])
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearOutput ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = [] ∧
      cfg'.stk GreedyEnumStack.workR = [] ∧
      cfg'.stk GreedyEnumStack.output = [] ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction workR generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearOutput,
             { cfg.var with peekBit := some false },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hwr : S GreedyEnumStack.workR = [] := h_workR
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearWorkR, Turing.TM2.stepAux, hwr, List.head?, Option.isSome,
                 BEq.beq]
      rw [show Option.instBEq.beq (some false) (some false) = true from by decide]
      simp [cond_true]
  | cons w rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearWorkR ∧
        cfg₁.stk GreedyEnumStack.workR = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.input = [] ∧
        cfg₁.stk GreedyEnumStack.workL = [] ∧
        cfg₁.stk GreedyEnumStack.output = [] ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearWorkR,
               { cfg.var with peekBit := some true },
               fun k => match k with
                 | GreedyEnumStack.workR => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_input, h_workL,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hwr : S GreedyEnumStack.workR = w :: rest := h_workR
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearWorkR, Turing.TM2.stepAux, hwr, List.head?,
                   Option.isSome, List.tail_cons, BEq.beq]
        rw [show Option.instBEq.beq (some true) (some false) = false from by decide]
        simp only [cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hwr₁, ht₁, hc₁, hi₁, hwl₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_output
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (h_label : cfg.l = some GreedyEnumLabel.clearOutput)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = [])
    (h_workR : cfg.stk GreedyEnumStack.workR = [])
    (h_output : cfg.stk GreedyEnumStack.output = [])
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementInvariant target counter cfg' := by
  refine ⟨⟨some GreedyEnumLabel.counter_increment,
           { cfg.var with peekOut := none },
           cfg.stk⟩, ?_, ?_⟩
  · apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have ho : S GreedyEnumStack.output = [] := h_output
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearOutput, Turing.TM2.stepAux, ho, List.head?,
                 Option.isNone, cond_true]
  · exact ⟨rfl, h_target, h_counter, h_input, h_workL, h_workR,
           h_output, h_saveTarget, h_saveCounter⟩

lemma clearInput_to_counterIncrement
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : ClearInputInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementInvariant target counter cfg' := by
  obtain ⟨cfg₁, hr₁, hl₁, ht₁, hc₁, hi₁, hwl₁, hwr₁, ho₁, hst₁, hsc₁⟩ :=
    clear_stack_input gen target counter
      (cfg.stk GreedyEnumStack.input)
      (cfg.stk GreedyEnumStack.workL)
      (cfg.stk GreedyEnumStack.workR)
      cfg hinv.h_label hinv.h_target hinv.h_counter rfl rfl rfl
      hinv.h_output hinv.h_saveTarget hinv.h_saveCounter
  obtain ⟨cfg₂, hr₂, hl₂, ht₂, hc₂, hi₂, hwl₂, hwr₂, ho₂, hst₂, hsc₂⟩ :=
    clear_stack_workL gen target counter
      (cfg.stk GreedyEnumStack.workL)
      (cfg.stk GreedyEnumStack.workR)
      cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
  obtain ⟨cfg₃, hr₃, hl₃, ht₃, hc₃, hi₃, hwl₃, hwr₃, ho₃, hst₃, hsc₃⟩ :=
    clear_stack_workR gen target counter
      (cfg.stk GreedyEnumStack.workR)
      cfg₂ hl₂ ht₂ hc₂ hi₂ hwl₂ hwr₂ ho₂ hst₂ hsc₂
  obtain ⟨cfg₄, hr₄, hinv₄⟩ :=
    clear_stack_output gen target counter
      cfg₃ hl₃ ht₃ hc₃ hi₃ hwl₃ hwr₃ ho₃ hst₃ hsc₃
  exact ⟨cfg₄, TM2Reaches_trans (TM2Reaches_trans (TM2Reaches_trans hr₁ hr₂) hr₃) hr₄, hinv₄⟩

end ClearPhase

lemma eval_dom_iff_TM2Halts
    (gen : Generator Γw Γo Q) (target : List Γo) :
    (@Turing.TM2.eval.{u,u,u,u} GreedyEnumStack (stackAlphabet Γw Γo Q)
      GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) _ _ _
      (greedyEnumMachine gen) GreedyEnumStack.target target).Dom ↔
    TM2Halts gen (Turing.TM2.init GreedyEnumStack.target target) := by
  change (Turing.eval (GEStep gen) _).Dom ↔ _
  constructor
  · intro h
    obtain ⟨cfg', hcfg'⟩ := Part.dom_iff_mem.mp h
    rw [Turing.mem_eval] at hcfg'
    exact ⟨cfg', hcfg'.1, hcfg'.2⟩
  · intro ⟨cfg', h1, h2⟩
    exact Part.dom_iff_mem.mpr ⟨cfg', Turing.mem_eval.mpr ⟨h1, h2⟩⟩

lemma init_copyCounterInvariant
    (_ : Generator Γw Γo Q) -- Keep this to help with universe level pinning.
    (target : List Γo) :
    CopyCounterInvariant target []
      (@Turing.TM2.init GreedyEnumStack.{u}
        (stackAlphabet Γw Γo Q)
        GreedyEnumLabel.{u}
        (GreedyEnumSigma Γw Γo Q)
        _ _ _
        GreedyEnumStack.target target) := by
  exact ⟨rfl, by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update]⟩

end GreedyEnum

end RandomisedGeneration
