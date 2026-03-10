import Mathlib
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-- The stacks used by the dovetail TM2 machine.

    Stack layout at quiescent points (start of each round):

    ── Main stacks ──
    • target:  [t₀, t₁, ..., tₖ]  — the word to recognise, first symbol on top.
               Unchanged throughout execution.
    • counter: [b₀, b₁, ..., bₘ]  — binary representation of the next input number
               to spawn (LSB on top, no leading falses). [] represents 0.
    • state:   [qₙ₋₁, qₙ₋₂, ..., q₀]  — one state per instance, newest on top.
               No separators needed (fixed number of elements per instance: exactly 1).
    • input:   Newest instance's segment on top. Each segment is:
               [none, some b₁, some b₂, ...]  — a none separator followed by the
               remaining unread input bits (as Option (ULift Bool)).
               The oldest instance's segment is at the bottom.
               Bits are the binary digits of the instance's input number;
               consumed bits have been popped.
    • workL:   Newest instance's segment on top. Each segment is:
               [none, some w₁, some w₂, ...]  — a none separator followed by
               the work tape cells to the left of the head (closest to head first).
               Cells are Option Γw; none is the separator between instances.
    • workR:   Same structure as workL but for cells to the right of the head.
               The head cell itself is included as the first element after the separator.
    • output:  Newest instance's segment on top. Each segment is:
               [none, some o₁, some o₂, ...]  — a none separator followed by
               the output symbols produced so far (most recent on top).

    ── Save stacks ──
    Mirror the corresponding main stacks. Used during the check phase and step phase
    to temporarily hold instance data while iterating through instances.
    Empty at quiescent points. -/
inductive DovetailStack : Type u
  | target
  | counter
  | input
  | state
  | workL
  | workR
  | output
  | saveTarget
  | saveCounter
  | saveInput
  | saveState
  | saveWorkL
  | saveWorkR
  | saveOutput

deriving instance DecidableEq for DovetailStack
deriving instance Fintype for DovetailStack
deriving instance Inhabited for DovetailStack

/-- The type of elements stored on each stack.
    • target, saveTarget: Γo (bare output symbols)
    • counter, saveCounter: ULift Bool (binary digits)
    • state, saveState: Q (generator states)
    • input, saveInput: Option (ULift Bool) — some b for a bit, none as separator
    • workL/R, saveWorkL/R: Option Γw — some x for a tape symbol, none as separator
    • output, saveOutput: Option Γo — some x for an output symbol, none as separator -/
def stackAlphabet (Γw Γo Q : Type u)
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    DovetailStack → Type u
  | DovetailStack.target      => Γo
  | DovetailStack.counter     => ULift.{u} Bool
  | DovetailStack.input       => Option (ULift.{u} Bool)
  | DovetailStack.state       => Q
  | DovetailStack.workL       => Option Γw
  | DovetailStack.workR       => Option Γw
  | DovetailStack.output      => Option Γo
  | DovetailStack.saveTarget  => Γo
  | DovetailStack.saveCounter => ULift.{u} Bool
  | DovetailStack.saveInput   => Option (ULift.{u} Bool)
  | DovetailStack.saveState   => Q
  | DovetailStack.saveWorkL   => Option Γw
  | DovetailStack.saveWorkR   => Option Γw
  | DovetailStack.saveOutput  => Option Γo

/-- Labels for the dovetail TM2 machine, corresponding to subroutine entry points.

    The machine executes in a loop of 5 phases:

    Phase 1 — Check: iterate through all existing instances (newest first).
      For each halting instance, compare its output against the target word.
      If a match is found, halt (accept). Otherwise, save the instance's
      segments to save stacks and continue to the next instance.

    Phase 2 — Spawn: copy the binary counter to create a new instance's
      input bitstream, push the initial state onto the state stack.

    Phase 3 — Step: iterate through all instances (newest first),
      applying one generator transition to each. Halted instances are
      preserved unchanged. Each instance's segments are saved to save
      stacks after processing.

    Phase 4 — Restore: move all segments from save stacks back to main
      stacks, adding none separators between instances.

    Phase 5 — Increment: increment the binary counter for the next spawn. -/
inductive DovetailLabel : Type u
  -- Phase 1: Check all instances for halting + output match
  | check_stripSeparators           -- pop none separators from input/workL/workR/output, push to save stacks
  | check_iterateInstances          -- loop: peek state stack, pop next or finish
  | check_testHalting               -- peek input/workR, apply δ, branch on halting
  | check_compareOutput             -- compare output vs target element by element
  | check_compareOutput_restoreTarget -- restore target from saveTarget after mismatch
  | check_compareOutput_restoreOutput -- restore output from saveOutput after mismatch
  | check_saveInstance_state        -- pop state, push to saveState
  | check_saveInstance_input        -- move input segment to saveInput (up to none separator)
  | check_saveInstance_workL        -- move workL segment to saveWorkL (up to none separator)
  | check_saveInstance_workR        -- move workR segment to saveWorkR (up to none separator)
  | check_saveInstance_output       -- move output segment to saveOutput (up to none separator)
  -- Phase 1→2 transition: restore save stacks without adding separators
  | check_restoreAll_state          -- restore states from saveState to state
  | check_restoreAll_input          -- restore input segments from saveInput to input
  | check_restoreAll_workL          -- restore workL segments from saveWorkL to workL
  | check_restoreAll_workR          -- restore workR segments from saveWorkR to workR
  | check_restoreAll_output         -- restore output segments from saveOutput to output
-- Phase 2: Spawn a new instance
  | spawn_copyCounter               -- pop counter bits to saveCounter
  | spawn_restoreAndPush            -- restore counter, push bits to input, push init state
  -- Phase 3: Step all instances
  | step_stripSeparators            -- pop none separators from input/workL/workR/output, push to save stacks
  | step_iterateInstances           -- loop: peek state stack, pop next or finish
  | step_peekInput                  -- peek input to read current bit (non-destructive)
  | step_peekWorkR                  -- peek/pop workR head cell, apply δ
  | step_applyTransition            -- push new state/workR, emit output, branch halted
  | step_consumeInput               -- conditionally pop input bit if direction = R
  | step_moveWorkHead               -- move work tape head: pop/push between workL and workR
  | step_saveInstance_state         -- pop state, push to saveState
  | step_saveInstance_input         -- move input segment to saveInput
  | step_saveInstance_workL         -- move workL segment to saveWorkL
  | step_saveInstance_workR         -- move workR segment to saveWorkR
  | step_saveInstance_output        -- move output segment to saveOutput
  -- Phase 4: Restore from step phase (adds none separators between instances)
  | step_restoreAll_state           -- restore states from saveState to state
  | step_restoreAll_input           -- restore + push none separator to input
  | step_restoreAll_workL           -- restore + push none separator to workL
  | step_restoreAll_workR           -- restore + push none separator to workR
  | step_restoreAll_output          -- restore + push none separator to output
  -- Phase 5: Increment binary counter
  | counter_increment               -- initialise carry := true
  | counter_increment_loop          -- process one bit: XOR with carry, AND for new carry
  | counter_increment_restore       -- restore counter bits from saveCounter
deriving DecidableEq, Fintype

set_option linter.style.whitespace false
set_option linter.style.longLine false
/-- The internal variable (σ) of the dovetail TM2 machine.
    This is the "register file" — all fields are scratch space used
    by the various subroutines. Fields are grouped by purpose.

    Key convention: `peekQ` holds the ORIGINAL state as set by
    check_iterateInstances/step_iterateInstances when they pop the state stack.
    After applyDelta overwrites `transQ`, `peekQ` still holds the original,
    which is important for the check phase (which must be non-destructive). -/
structure DovetailSigma (Γw Γo Q : Type u)
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] where

  -- ── Generator transition results (populated by applyDelta) ────────────
  transQ      : Option Q           -- new state (or original if halted)
  transW      : Option Γw          -- symbol to write to workR
  transIDir   : InputTapeDirection  -- input tape direction
  transWDir   : WorkTapeDirection   -- work tape direction
  transOut    : Option (Option Γo)  -- none = no output field, some o = output action
  transHalted : Bool                -- true iff gen.δ returned none

  -- ── Current input bit (set by step_peekInput / check_testHalting) ─────
  inputBit    : ULift.{u} Bool     -- the bit value (false if input stack empty/separator)

  -- ── Scratch space for peek/pop results ────────────────────────────────
  peekQ       : Option Q                        -- peeked/popped state
  peekBit     : Option (ULift.{u} Bool)         -- peeked counter/saveCounter bit
  peekInput   : Option (Option (ULift.{u} Bool)) -- peeked input element
  peekWorkL   : Option (Option Γw)              -- peeked workL element
  peekWorkR   : Option (Option Γw)              -- peeked workR element
  peekOut     : Option (Option Γo)              -- peeked output/saveOutput element
  peekTarget  : Option Γo                       -- peeked target element

  -- ── Binary counter scratch ────────────────────────────────────────────
  carry       : Option (ULift.{u} Bool)         -- carry bit for increment
set_option linter.style.whitespace true
set_option linter.style.longLine true

instance : Inhabited DovetailLabel := ⟨DovetailLabel.check_stripSeparators⟩

instance : Inhabited (DovetailSigma Γw Γo Q) :=
  ⟨{ transQ      := none
     transW      := none
     transIDir   := InputTapeDirection.N
     transWDir   := WorkTapeDirection.N
     transOut    := none
     transHalted := false
     inputBit    := ULift.up false
     peekQ       := none
     peekBit     := none
     peekInput   := none
     peekWorkL   := none
     peekWorkR   := none
     peekOut     := none
     peekTarget  := none
     carry       := none }⟩

instance : Fintype (ULift.{u} Bool) :=
  Fintype.ofEquiv Bool ⟨ULift.up, ULift.down, fun _ => rfl, fun _ => rfl⟩

instance : DecidableEq (ULift.{u} Bool) :=
  fun a b => decidable_of_iff (a.down = b.down) (by cases a; cases b; simp [ULift.ext_iff])

instance [Fintype Γw] [Fintype Γo] [Fintype Q] [DecidableEq Γw] [DecidableEq Γo] [DecidableEq Q] :
    Fintype (DovetailSigma Γw Γo Q) :=
  Fintype.ofEquiv
    (Option Q × Option Γw × InputTapeDirection × WorkTapeDirection ×
     Option (Option Γo) × Bool × ULift.{u} Bool × Option Q ×
     Option (ULift.{u} Bool) × Option (Option (ULift.{u} Bool)) ×
     Option (Option Γw) × Option (Option Γw) ×
     Option (Option Γo) × Option Γo × Option (ULift.{u} Bool))
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ =>
        { transQ := a, transW := b, transIDir := c, transWDir := d,
          transOut := e, transHalted := f, inputBit := g, peekQ := h,
          peekBit := i, peekInput := j, peekWorkL := k, peekWorkR := l,
          peekOut := m, peekTarget := n, carry := o }
      invFun := fun σ =>
        (σ.transQ, σ.transW, σ.transIDir, σ.transWDir,
         σ.transOut, σ.transHalted, σ.inputBit, σ.peekQ,
         σ.peekBit, σ.peekInput, σ.peekWorkL, σ.peekWorkR,
         σ.peekOut, σ.peekTarget, σ.carry)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def dovetailInit {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (target : List Γo) :
    Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.init DovetailStack.target target

/-- Apply the generator's transition function to the current instance.
    Reads transQ (current state), inputBit (current input), and transW (head symbol).
    On halt (δ returns none): sets transHalted := true, directions to N, no output.
    On step (δ returns some): updates transQ, transW, transOut, directions, transHalted := false.

    Note: transQ is overwritten here. The check phase uses peekQ (which holds
    the original state) to push back the unmodified state. The step phase uses
    the new transQ. -/
def applyDelta {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (σ : DovetailSigma Γw Γo Q) : DovetailSigma Γw Γo Q :=
  match σ.transW with
  | some w =>
      match gen.δ (σ.transQ.getD gen.init) σ.inputBit.down w with
      | none =>
          { σ with
            transIDir   := InputTapeDirection.N
            transWDir   := WorkTapeDirection.N
            transOut    := none
            transHalted := true }
      | some (q', w', o, id, wd) =>
          { σ with
            transQ      := some q'
            transW      := some w'
            transOut    := some o
            transIDir   := id
            transWDir   := wd
            transHalted := false }
  | none => σ

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 1: Check all instances for halting + output match
══════════════════════════════════════════════════════════════════════════════

  Overview:
    check_stripSeparators is the entry point for the check phase (called from
    counter_increment_restore). It removes the none separators from input,
    workL, workR, and output for the newest instance and pushes them to the
    corresponding save stacks, exposing the newest instance's segment data.

    check_iterateInstances then loops through instances from newest to oldest.
    For each instance:
      1. Pop its state from the state stack
      2. Peek input and workR to determine the current input bit and head symbol
      3. Apply δ to check if the instance would halt
      4. If halting: push ORIGINAL state back, compare output against target
         - If output matches target: HALT (accept)
         - If mismatch: restore target and output stacks, then save instance
      5. If not halting: push ORIGINAL state back, save instance segments
      6. Save instance = move state/input/workL/workR/output to save stacks.
         The save routines also consume the next instance's none separator
         (if present) and push it to save, exposing the next instance's data
         for the following iteration.
    After all instances: restore save stacks (without adding separators),
    then proceed to Phase 2 (spawn).

  Critical invariant: the check phase is NON-DESTRUCTIVE. It peeks at
  input and workR without popping, and pushes back the original state
  (from peekQ), not the delta result. The only stack that gets temporarily
  modified is target/output during comparison, which is restored on mismatch.
-/

/-- Strip the none separators from input, workL, workR, output and push them
    to the corresponding save stacks. Called once before entering the check loop.
    After this, the newest instance's segment data is directly exposed. -/
def check_stripSeparators {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( -- No instances yet (round 0): skip strip, go directly to spawn
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_state) )
    ( -- Strip separators from input, workL, workR, output, push to save
      Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput (fun _ => none)
      <| Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL (fun _ => none)
      <| Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR (fun _ => none)
      <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) )

-- Peek state stack: if empty, all checked → restore and proceed to spawn phase
def check_iterateInstances {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_testHalting) )

-- Peek input and workR to determine if this instance is halting.
-- Separators have already been stripped by check_stripSeparators.
-- Non-destructive: pushes the ORIGINAL state back, not the delta result.
def check_testHalting {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  -- peek input to get the current bit (non-destructive)
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with
    inputBit  := match i with
                 | some (some b) => b
                 | _             => ULift.up false
    peekInput := i })
  -- peek workR to get the head symbol (non-destructive)
  <| Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with
    transW    := match w with
                 | some (some x) => some x
                 | _             => some gen.blank
    peekWorkR := w })
  -- apply delta to check if halting
  <| Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
  <| Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
    ( -- halting: push ORIGINAL state back, compare output against target
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput) )
    ( -- not halting: push ORIGINAL state back, save segments
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_state) )

/-- Compare the output of a halting instance against the target word.

    Both stacks are consumed top-to-bottom simultaneously:
    • target stack: [t₀, t₁, ...] with t₀ on top
    • output stack: [some o_k, ..., some o₁, none, ...] with most recent output on top

    The output stack has the instance's output segment on top (separator already
    stripped by check_stripSeparators), with symbols in reverse order (most
    recently emitted on top). The segment ends at the next instance's none
    separator or the bottom of the stack.

    Since the target is also stored with first element on top, a match occurs
    when output.reverse = target, i.e., when consuming both top-to-bottom
    yields matching elements.

    On match (both exhausted simultaneously): halt.
    On mismatch or length difference: goto restoreTarget to undo the comparison.

    During comparison, consumed elements are pushed to saveTarget and saveOutput
    so they can be restored on mismatch. -/
def check_compareOutput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.target (fun σ t => { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( -- target exhausted: check output also exhausted
      Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
            | none      => true
            | some none => true
            | _         => false)
        ( Turing.TM2.Stmt.halt )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreTarget) ) )
    ( Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
            | none      => true
            | some none => true
            | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreTarget) )
        ( Turing.TM2.Stmt.branch (fun σ => match σ.peekTarget, σ.peekOut with
              | some t, some (some o) => decide (t = o)
              | _, _                  => false)
            ( Turing.TM2.Stmt.pop DovetailStack.target (fun σ _ => σ)
              <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
              <| Turing.TM2.Stmt.push DovetailStack.saveTarget
                (fun σ => σ.peekTarget.getD default)
              <| Turing.TM2.Stmt.push DovetailStack.saveOutput
                (fun σ => σ.peekOut.getD none)
              <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput) )
            ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreTarget) ) ) )

def check_compareOutput_restoreTarget {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveTarget (fun σ t => { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreOutput) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveTarget (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.target
        (fun σ => σ.peekTarget.getD default)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreTarget) )

def check_compareOutput_restoreOutput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput_restoreOutput) )

-- Check phase save segment: save this instance's segments then return to check_iterateInstances
def check_saveInstance_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.pop DovetailStack.state (fun σ q => { σ with peekQ := q })
  <| Turing.TM2.Stmt.push DovetailStack.saveState
    (fun σ => σ.peekQ.getD gen.init)
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_input)

def check_saveInstance_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveInput (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_input) )

def check_saveInstance_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveWorkL (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) )

def check_saveInstance_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveWorkR (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) )

def check_saveInstance_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveOutput (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) )

/-
  Phase 1→2 transition: restore all segments from save stacks.

  Unlike step_restoreAll_*, these do NOT push none separators when the
  save stack is exhausted. This is because the check phase save/restore
  should be invisible — the main stacks must look exactly as they did
  before the check phase started.
-/
def check_restoreAll_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveState (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_input) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveState (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_state) )

def check_restoreAll_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveInput (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_input) )

def check_restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_workL) )

def check_restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_workR) )

def check_restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.spawn_copyCounter) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_output) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 2: Spawn a new instance
══════════════════════════════════════════════════════════════════════════════

  The binary counter holds the input number N for the next instance to spawn.

  spawn_copyCounter: pop all bits from counter to saveCounter (reversing order).
  spawn_restoreAndPush: pop bits from saveCounter one at a time, and for each:
    • Push the bit back to counter (restoring it)
    • Push the bit to the input stack (creating the new instance's input segment)
  When saveCounter is empty:
    • Push gen.init onto the state stack
    • Push none separators onto input, workL, workR, and output

  After this phase, the state stack has one more entry (the new instance),
  and the input stack has a new segment [none, bit_k, ..., bit_0] on top
  (none separator followed by the input bits). The workL, workR, and output
  stacks each have a none separator on top (the new instance starts with
  empty work tapes and no output).

  The counter is restored to its original value N. It will be incremented
  to N+1 in Phase 5.
-/

def spawn_copyCounter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.spawn_restoreAndPush) )
    ( Turing.TM2.Stmt.pop DovetailStack.counter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.saveCounter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.spawn_copyCounter) )

def spawn_restoreAndPush {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( -- All bits restored. Push init state and none separators for the new instance,
      -- then strip the separators (moving them to save stacks) before entering the step loop.
      Turing.TM2.Stmt.push DovetailStack.state (fun _ => gen.init)
      <| Turing.TM2.Stmt.push DovetailStack.input (fun _ => none)
      <| Turing.TM2.Stmt.push DovetailStack.workL (fun _ => none)
      <| Turing.TM2.Stmt.push DovetailStack.workR (fun _ => none)
      <| Turing.TM2.Stmt.push DovetailStack.output (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_stripSeparators) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.counter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekBit)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.spawn_restoreAndPush) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 3: Step all instances
══════════════════════════════════════════════════════════════════════════════

  Before entering the loop, step_stripSeparators removes the none separators
  from input, workL, workR, and output (for the newest instance) and pushes
  them to the corresponding save stacks.

  Then iterates through instances from newest to oldest. For each instance:
    1. Pop state from state stack
    2. Peek input to read current bit (non-destructive peek)
    3. Peek/pop workR to read head symbol (pop if real symbol, else use blank)
    4. Apply δ (applyDelta)
    5. If halted: push ORIGINAL state and work symbol back (preserving config)
    6. If running: push NEW state and written symbol, optionally push output,
       conditionally consume input bit (if direction = R),
       move work head (shuffle between workL and workR)
    7. Save instance segments to save stacks. The save routines also consume
       the next instance's none separator (if present) and push it to save,
       exposing the next instance's data for the following iteration.

  After all instances: proceed to Phase 4 (restore).

  Key difference from check phase: the step phase IS destructive.
  It modifies the instance by applying the transition function.
  Halted instances are preserved unchanged (state and head symbol pushed back).
-/

/-- Strip the none separators from input, workL, workR, output and push them
    to the corresponding save stacks. Called once before entering the step loop
    (from spawn_restoreAndPush), not on every iteration. -/
def step_stripSeparators {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  -- pop none from input, push to saveInput
  Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
  <| Turing.TM2.Stmt.push DovetailStack.saveInput (fun _ => none)
  -- pop none from workL, push to saveWorkL
  <| Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
  <| Turing.TM2.Stmt.push DovetailStack.saveWorkL (fun _ => none)
  -- pop none from workR, push to saveWorkR
  <| Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
  <| Turing.TM2.Stmt.push DovetailStack.saveWorkR (fun _ => none)
  -- pop none from output, push to saveOutput
  <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
  <| Turing.TM2.Stmt.push DovetailStack.saveOutput (fun _ => none)
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances)

def step_iterateInstances {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_peekInput) )

def step_peekInput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with
    inputBit  := match i with
                 | some (some b) => b
                 | _             => ULift.up false
    peekInput := i })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_peekWorkR)

def step_peekWorkR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with
    transW    := match w with
                 | some (some x) => some x
                 | _             => some gen.blank
    peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
      | some (some _) => true
      | _             => false)
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_applyTransition) )
    ( Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_applyTransition) )

/-- Apply the transition result to the stacks.

    For HALTED instances (transHalted = true):
      Push the original state (transQ, which equals peekQ since applyDelta
      doesn't change transQ on halt) and the original work symbol back.
      Then go directly to save — no input/output/work-head changes.

    For RUNNING instances (transHalted = false):
      Push the NEW state (transQ, as updated by applyDelta) and the
      NEW work symbol (transW). Optionally push an output symbol.
      Then consume input and move work head. -/
def step_applyTransition {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
    ( -- instance halted: push state and work symbol back, go to step_saveInstance_state
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.transW.map some |>.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) )
    ( -- instance still running: push new state and written symbol
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.transW.map some |>.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.transOut with
          | some (some _) => true
          | _             => false)
        ( Turing.TM2.Stmt.push DovetailStack.output
            (fun σ => match σ.transOut with
              | some o => o
              | none   => none)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_consumeInput) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_consumeInput) ) )

def step_consumeInput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => match σ.transIDir, σ.peekInput with
      | InputTapeDirection.R, some (some _) => true
      | _, _                                => false)
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_moveWorkHead) )
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_moveWorkHead) )

def step_moveWorkHead {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => match σ.transWDir with
      | WorkTapeDirection.L => true
      | _                   => false)
    ( Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some (some _) => true
          | _             => false)
        ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
          <| Turing.TM2.Stmt.push DovetailStack.workR
            (fun σ => match σ.peekWorkL with
              | some (some x) => some x
              | _             => some gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) )
        ( Turing.TM2.Stmt.push DovetailStack.workR
            (fun _ => some gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) ) )
    ( Turing.TM2.Stmt.branch (fun σ => match σ.transWDir with
        | WorkTapeDirection.R => true
        | _                   => false)
      ( Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
        <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
            | some (some _) => true
            | _             => false)
          ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
            <| Turing.TM2.Stmt.push DovetailStack.workL
              (fun σ => match σ.peekWorkR with
                | some (some x) => some x
                | _             => some gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) )
          ( Turing.TM2.Stmt.push DovetailStack.workL
              (fun _ => some gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) ) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_state) ) )

-- Step phase save segment: save this instance's segments then return to step_iterateInstances
def step_saveInstance_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.pop DovetailStack.state (fun σ q => { σ with peekQ := q })
  <| Turing.TM2.Stmt.push DovetailStack.saveState
    (fun σ => σ.peekQ.getD gen.init)
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_input)

def step_saveInstance_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveInput (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_input) )

def step_saveInstance_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveWorkL (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) )

def step_saveInstance_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveWorkR (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) )

def step_saveInstance_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
      | none      => true
      | some none => true
      | _         => false)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
        | some none => true
        | _         => false)
      ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
        <| Turing.TM2.Stmt.push DovetailStack.saveOutput (fun _ => none)
        <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 4: Restore from step phase
══════════════════════════════════════════════════════════════════════════════

  Move all segments from save stacks back to main stacks.

  The save stacks contain the instance data interleaved with none separators
  (pushed by step_stripSeparators). The restore simply copies everything back
  faithfully, including the separators. No extra separators are added.

  After restoration, every instance has a none separator above its
  segment on input, workL, workR, and output stacks — matching the
  quiescent format [none, stuff, none, stuff, ...].
-/

def step_restoreAll_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveState (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_input) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveState (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_state) )

def step_restoreAll_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveInput (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_input) )

def step_restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workL) )

def step_restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workR) )

def step_restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_output) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 5: Increment binary counter
══════════════════════════════════════════════════════════════════════════════

  The counter stores a binary number with LSB on top and no leading falses.
  Incrementing is done with a carry bit propagated through the bits:

  counter_increment: set carry := true, enter loop.
  counter_increment_loop: for each bit in counter (popped to saveCounter):
    newBit   := bit XOR carry
    newCarry := bit AND carry
    Push newBit to saveCounter.
  When counter is empty: if carry still set, push true to counter.
  counter_increment_restore: pop all bits from saveCounter back to counter.

  Examples: [] → [true]  (0 → 1)
            [true] → [false, true]  (1 → 2)
            [false, true] → [true, true]  (2 → 3)
            [true, true] → [false, false, true]  (3 → 4)
-/

def counter_increment {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.load (fun σ => { σ with carry := some (ULift.up true) })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment_loop)

def counter_increment_loop {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.carry with
          | some b => ULift.down b
          | none   => false)
        ( Turing.TM2.Stmt.push DovetailStack.counter (fun _ => ULift.up true)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment_restore) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment_restore) ) )
    ( Turing.TM2.Stmt.pop DovetailStack.counter (fun σ _ => σ)
      <| Turing.TM2.Stmt.load (fun σ =>
          let bit      := (σ.peekBit.getD (ULift.up false)).down
          let carry    := (σ.carry.getD (ULift.up false)).down
          let newBit   := Bool.xor bit carry
          let newCarry := Bool.and bit carry
          { σ with
            peekBit := some (ULift.up newBit)
            carry   := some (ULift.up newCarry) })
      <| Turing.TM2.Stmt.push DovetailStack.saveCounter
          (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment_loop) )

def counter_increment_restore {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_stripSeparators) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.counter
          (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment_restore) )

/-
══════════════════════════════════════════════════════════════════════════════
  Machine definition
══════════════════════════════════════════════════════════════════════════════
-/

def dovetailMachine {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    DovetailLabel → Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q)
  -- Phase 1: Check
  | DovetailLabel.check_stripSeparators => check_stripSeparators
  | DovetailLabel.check_iterateInstances => check_iterateInstances
  | DovetailLabel.check_testHalting => check_testHalting gen
  | DovetailLabel.check_compareOutput => check_compareOutput
  | DovetailLabel.check_compareOutput_restoreTarget => check_compareOutput_restoreTarget
  | DovetailLabel.check_compareOutput_restoreOutput => check_compareOutput_restoreOutput
  | DovetailLabel.check_saveInstance_state => check_saveInstance_state gen
  | DovetailLabel.check_saveInstance_input => check_saveInstance_input
  | DovetailLabel.check_saveInstance_workL => check_saveInstance_workL
  | DovetailLabel.check_saveInstance_workR => check_saveInstance_workR
  | DovetailLabel.check_saveInstance_output => check_saveInstance_output
  | DovetailLabel.check_restoreAll_state => check_restoreAll_state gen
  | DovetailLabel.check_restoreAll_input => check_restoreAll_input
  | DovetailLabel.check_restoreAll_workL => check_restoreAll_workL
  | DovetailLabel.check_restoreAll_workR => check_restoreAll_workR
  | DovetailLabel.check_restoreAll_output => check_restoreAll_output
  -- Phase 2: Spawn
  | DovetailLabel.spawn_copyCounter => spawn_copyCounter
  | DovetailLabel.spawn_restoreAndPush => spawn_restoreAndPush gen
  -- Phase 3: Step
  | DovetailLabel.step_stripSeparators => step_stripSeparators
  | DovetailLabel.step_iterateInstances => step_iterateInstances
  | DovetailLabel.step_peekInput => step_peekInput
  | DovetailLabel.step_peekWorkR => step_peekWorkR gen
  | DovetailLabel.step_applyTransition => step_applyTransition gen
  | DovetailLabel.step_consumeInput => step_consumeInput
  | DovetailLabel.step_moveWorkHead => step_moveWorkHead gen
  | DovetailLabel.step_saveInstance_state => step_saveInstance_state gen
  | DovetailLabel.step_saveInstance_input => step_saveInstance_input
  | DovetailLabel.step_saveInstance_workL => step_saveInstance_workL
  | DovetailLabel.step_saveInstance_workR => step_saveInstance_workR
  | DovetailLabel.step_saveInstance_output => step_saveInstance_output
  -- Phase 4: Restore + increment
  | DovetailLabel.step_restoreAll_state => step_restoreAll_state gen
  | DovetailLabel.step_restoreAll_input => step_restoreAll_input
  | DovetailLabel.step_restoreAll_workL => step_restoreAll_workL
  | DovetailLabel.step_restoreAll_workR => step_restoreAll_workR
  | DovetailLabel.step_restoreAll_output => step_restoreAll_output
  | DovetailLabel.counter_increment => counter_increment
  | DovetailLabel.counter_increment_loop => counter_increment_loop
  | DovetailLabel.counter_increment_restore => counter_increment_restore

end Dovetailing

end RandomisedGeneration
