import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

structure DovetailState where
  instances : List (GenConfig Γw Γo Q)
  nextInput : ℕ

def stepOrHalt
  (gen : Generator Γw Γo Q)
  (cfg : GenConfig Γw Γo Q) : GenConfig Γw Γo Q :=
  match step gen cfg with
  | none => cfg
  | some c' => c'

def dovetailStep
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { instances := (ds.instances ++ [initConfig gen (Nat.testBit ds.nextInput)]).map
                   (stepOrHalt gen)
    nextInput := ds.nextInput + 1 }

def initDovetailState : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { instances := []
    nextInput := 0 }

def DovetailRecognises
  (gen : Generator Γw Γo Q)
  (w : List Γo) : Prop :=
  ∃ (n i : Nat) (cfg : GenConfig Γw Γo Q),
    let state :=
      (dovetailStep gen)^[n]
        (initDovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    let insts := state.instances
    insts[i]? = some cfg ∧
    IsHalting gen cfg ∧
    cfg.output = w

-- The "already stepped" prefix
def steppedPrefix
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (GenConfig Γw Γo Q) :=
  (ds.instances.take k).map (stepOrHalt gen)

-- The "not yet stepped" suffix
def pendingSuffix
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (GenConfig Γw Γo Q) :=
  ds.instances.drop k

-- The mid-round state at frontier k
def midRoundState
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { ds with instances := steppedPrefix gen ds k ++ pendingSuffix ds k }

-- At k=0, nothing has been stepped yet
lemma midRoundState_zero
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  midRoundState gen ds 0 = ds := by
  simp [midRoundState, steppedPrefix, pendingSuffix]

-- At k=length, everything has been stepped
lemma midRoundState_length
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  midRoundState gen ds ds.instances.length =
    { ds with instances := ds.instances.map (stepOrHalt gen) } := by
  simp [midRoundState, steppedPrefix, pendingSuffix, List.take_length, List.drop_length]

-- Advancing the frontier by one
lemma midRoundState_succ
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ)
  (hk : k < ds.instances.length) :
  midRoundState gen ds (k + 1) =
  { ds with instances :=
      (ds.instances.take k).map (stepOrHalt gen)
      ++
      [ stepOrHalt gen (ds.instances.get ⟨k, hk⟩) ]
      ++
      ds.instances.drop (k + 1) } := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  congr 1
  rw [List.take_add_one, List.map_append]
  simp [List.getElem?_eq_getElem hk]

-- The full dovetailStep decomposes into midRoundState at length, then spawn
lemma dovetailStep_eq_midRound_of_spawn
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  dovetailStep gen ds =
    let spawned : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
      { instances := ds.instances ++ [initConfig gen (Nat.testBit ds.nextInput)]
        nextInput := ds.nextInput + 1 }
    midRoundState gen spawned spawned.instances.length := by
  simp [dovetailStep, midRoundState, steppedPrefix, pendingSuffix]

-- The length of instances is preserved by midRoundState
lemma midRoundState_length_eq
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) :
  (midRoundState gen ds k).instances.length = ds.instances.length := by
  simp [midRoundState, steppedPrefix, pendingSuffix]
  omega

-- Instances before the frontier in midRoundState are stepped versions of originals
lemma midRoundState_before_frontier
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k i : ℕ)
  (hi : i < k)
  (hk : k ≤ ds.instances.length) :
  (midRoundState gen ds k).instances[i]? =
    (ds.instances[i]?).map (stepOrHalt gen) := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  rw [List.getElem?_append]
  simp only [List.length_map, List.length_take]
  rw [if_pos (by omega)]
  rw [List.getElem?_map]
  simp [List.getElem?_take]
  simp [hi]

-- Instances from the frontier onwards are unchanged
lemma midRoundState_from_frontier
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k i : ℕ)
  (hi : k ≤ i) :
  (midRoundState gen ds k).instances[i]? =
    ds.instances[i]? := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  have : (List.map (stepOrHalt gen) (ds.instances.take k) ++
          ds.instances.drop k)[i]? = ds.instances[i]? := by
    conv_rhs => rw [← List.take_append_drop k ds.instances]
    simp only [List.getElem?_append, List.length_map, List.length_take]
    rw [if_neg (by omega)]
    simp [List.getElem?_drop]
    omega
  exact this

lemma instances_length_after_steps
  (gen : Generator Γw Γo Q) (n : ℕ) :
  ((dovetailStep gen)^[n] initDovetailState).instances.length = n := by
  induction n with
  | zero => simp [initDovetailState]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp [ih]

lemma nextInput_after_steps (gen : Generator Γw Γo Q) (n : ℕ) :
    ((dovetailStep gen)^[n] initDovetailState).nextInput = n := by
  induction n with
  | zero => simp [initDovetailState]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp [ih]

def stepNHalt
  (gen : Generator Γw Γo Q)
  (cfg : GenConfig Γw Γo Q)
  : ℕ → GenConfig Γw Γo Q
  | 0 => cfg
  | n + 1 =>
    let c := stepNHalt gen cfg n
    match step gen c with
    | none => c
    | some c' => c'

@[simp]
lemma stepNHalt_zero (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) :
    stepNHalt gen cfg 0 = cfg := rfl

@[simp]
lemma stepNHalt_succ (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (n : ℕ) :
    stepNHalt gen cfg (n + 1) =
    match step gen (stepNHalt gen cfg n) with
    | none => stepNHalt gen cfg n
    | some c' => c' := rfl

lemma stepOrHalt_stepNHalt (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (n : ℕ) :
    stepOrHalt gen (stepNHalt gen cfg n) = stepNHalt gen cfg (n + 1) := by
  simp only [stepOrHalt, stepNHalt_succ]

lemma stepNHalt_fixed (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (n : ℕ)
    (h : IsHalting gen (stepNHalt gen cfg n)) :
    ∀ m, n ≤ m → stepNHalt gen cfg m = stepNHalt gen cfg n := by
  intro m hm
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this
    rfl
  | succ m ih =>
    by_cases hm' : n ≤ m
    · simp [ih hm', IsHalting] at h ⊢; simp [h]
    · have : n = m + 1 := by omega
      subst this
      rfl

lemma instance_config_after_steps
  (gen : Generator Γw Γo Q)
  (n i : ℕ) (hi : i < n) :
  ((dovetailStep gen)^[n] initDovetailState).instances[i]? =
    some (stepNHalt gen (initConfig gen i.testBit) (n - i)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp only [List.getElem?_map, List.getElem?_append]
    by_cases hi' : i < n
    · rw [if_pos (by rw [instances_length_after_steps]; exact hi')]
      rw [ih hi']
      simp only [Option.map_some]
      rw [stepOrHalt_stepNHalt, show n + 1 - i = (n - i) + 1 by omega]
    · have hi'' : i = n := by omega
      subst hi''
      rw [if_neg (by rw [instances_length_after_steps]; omega)]
      rw [instances_length_after_steps, nextInput_after_steps]
      simp only [Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.map_some]
      simp [stepOrHalt]

lemma stepNHalt_step (gen : Generator Γw Γo Q) (cfg cfg' : GenConfig Γw Γo Q) (n : ℕ)
    (hstep : step gen cfg = some cfg') :
    stepNHalt gen cfg (n + 1) = stepNHalt gen cfg' n := by
  induction n with
  | zero => simp [stepNHalt, hstep]
  | succ n ih =>
    simp [stepNHalt_succ]
    simp [← ih]

lemma stepNHalt_eq_of_stepN (gen : Generator Γw Γo Q) (cfg c : GenConfig Γw Γo Q) (n : ℕ)
    (h : stepN gen (some cfg) n = some c) :
    stepNHalt gen cfg n = c := by
  induction n generalizing cfg with
  | zero => simp only [stepN_zero, Option.some.injEq] at h; exact h
  | succ n ih =>
    rw [stepN_succ_front] at h
    cases hstep : step gen cfg with
    | none => simp [hstep, stepN_none] at h
    | some cfg' =>
      simp only [Option.bind_some, hstep] at h
      rw [stepNHalt_step gen cfg cfg' n hstep]
      exact ih cfg' h

lemma stepNHalt_Computes (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (n : ℕ)
    (h : IsHalting gen (stepNHalt gen cfg n)) :
    Computes gen cfg (stepNHalt gen cfg n).output := by
  induction n generalizing cfg with
  | zero =>
    simp only [stepNHalt_zero] at h ⊢
    exact Computes.halt cfg h
  | succ n ih =>
    cases hstep : step gen cfg with
    | none =>
      have : stepNHalt gen cfg (n + 1) = cfg :=
        stepNHalt_fixed gen cfg 0 (by simp [IsHalting, hstep]) (n + 1) (by omega)
      rw [this]
      exact Computes.halt cfg hstep
    | some cfg' =>
      rw [stepNHalt_step gen cfg cfg' n hstep] at h ⊢
      exact Computes.step cfg cfg' _ hstep (ih cfg' h)

theorem DovetailRecognises_iff_Computes
  (gen : Generator Γw Γo Q)
  (w : List Γo) :
  DovetailRecognises gen w ↔
  ∃ input : ℕ → Bool, Computes gen (initConfig gen input) w := by
  constructor
  · -- Forward: DovetailRecognises → ∃ input, Computes
    intro ⟨n, i, cfg, h_inst, h_halt, h_out⟩
    refine ⟨Nat.testBit i, h_out ▸ ?_⟩
    have hi : i < n := by
      have hlen := instances_length_after_steps gen n
      have : ((dovetailStep gen)^[n] initDovetailState).instances[i]? ≠ none := by
        rw [h_inst]; exact Option.some_ne_none _
      rwa [ne_eq, List.getElem?_eq_none_iff, not_le, hlen] at this
    have h_cfg := instance_config_after_steps gen n i hi
    rw [h_inst] at h_cfg
    have h_eq : stepNHalt gen (initConfig gen (Nat.testBit i)) (n - i) = cfg := by
      simp at h_cfg
      exact h_cfg.symm
    rw [← h_eq]
    exact stepNHalt_Computes gen _ _ (h_eq ▸ h_halt)
  · -- Backward: ∃ m, Computes → DovetailRecognises
    intro ⟨f, h_computes⟩
    obtain ⟨m, h_computes'⟩ := h_computes.exists_natTestBit
    obtain ⟨k, haltCfg, h_stepN, h_halt, h_out⟩ := h_computes'.to_stepN
    -- After m + k + 1 rounds, instance m has taken k + 1 steps.
    -- stepNHalt at k = haltCfg (by stepN agreement), and at k + 1 = haltCfg (fixed point).
    refine ⟨m + k + 1, m, haltCfg, ?_, h_halt, h_out⟩
    have hm : m < m + k + 1 := by omega
    have h_inst := instance_config_after_steps gen (m + k + 1) m hm
    rw [show m + k + 1 - m = k + 1 by omega] at h_inst
    rw [stepNHalt_succ] at h_inst
    have h_eq := stepNHalt_eq_of_stepN gen (initConfig gen m.testBit) haltCfg k h_stepN
    rw [h_eq] at h_inst
    simp only [Function.iterate_succ, Function.comp_apply, h_halt] at h_inst
    exact h_inst

variable [Inhabited Γw] [FinEnum Q]

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

instance : Inhabited DovetailLabel := ⟨DovetailLabel.check_iterateInstances⟩

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
    Iterates through instances from newest (top of state stack) to oldest.
    For each instance:
      1. Pop its state from the state stack
      2. Peek input and workR to determine the current input bit and head symbol
      3. Apply δ to check if the instance would halt
      4. If halting: push ORIGINAL state back, compare output against target
         - If output matches target: HALT (accept)
         - If mismatch: restore target and output stacks, then save instance
      5. If not halting: push ORIGINAL state back, save instance segments
      6. Save instance = move state/input/workL/workR/output to save stacks
    After all instances: restore save stacks (without adding separators),
    then proceed to Phase 2 (spawn).

  Critical invariant: the check phase is NON-DESTRUCTIVE. It peeks at
  input and workR without popping, and pushes back the original state
  (from peekQ), not the delta result. The only stack that gets temporarily
  modified is target/output during comparison, which is restored on mismatch.
-/

-- Peek state stack: if empty, all checked → restore and proceed to spawn phase
def check_iterateInstances {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_restoreAll_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_testHalting) )

-- Peek input and workR to determine if this instance is halting
-- Non-destructive: pushes the ORIGINAL state back, not the delta result
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
    ( -- halting: push ORIGINAL state back, pop output none separator (save it), compare
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_compareOutput) )
    ( -- not halting: push ORIGINAL state back, save segments
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_state) )

/-- Compare the output of a halting instance against the target word.

    Both stacks are consumed top-to-bottom simultaneously:
    • target stack: [t₀, t₁, ...] with t₀ on top
    • output stack: [..., some o₂, some o₁, none, ...] with most recent output on top

    The output stack has the instance's output segment on top, with symbols
    in reverse order (most recently emitted on top), preceded by a none separator.
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
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_input) ) )

def check_saveInstance_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workL) ) )

def check_saveInstance_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_workR) ) )

def check_saveInstance_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_saveInstance_output) ) )

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
  When saveCounter is empty, push gen.init onto the state stack.

  After this phase, the state stack has one more entry (the new instance),
  and the input stack has a new segment of bits on top (no none separator
  yet — that will be added by step_restoreAll_input after the step phase).

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
    ( Turing.TM2.Stmt.push DovetailStack.state (fun _ => gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances) )
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

  Iterates through instances from newest to oldest. For each instance:
    1. Pop state from state stack
    2. Peek input to read current bit (non-destructive peek)
    3. Peek/pop workR to read head symbol (pop if real symbol, else use blank)
    4. Apply δ (applyDelta)
    5. If halted: push ORIGINAL state and work symbol back (preserving config)
    6. If running: push NEW state and written symbol, optionally push output,
       conditionally consume input bit (if direction = R),
       move work head (shuffle between workL and workR)
    7. Save instance segments to save stacks

  After all instances: proceed to Phase 4 (restore).

  Key difference from check phase: the step phase IS destructive.
  It modifies the instance by applying the transition function.
  Halted instances are preserved unchanged (state and head symbol pushed back).
-/

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
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_input) ) )

def step_saveInstance_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workL) ) )

def step_saveInstance_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_workR) ) )

def step_saveInstance_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_iterateInstances) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_saveInstance_output) ) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 4: Restore from step phase
══════════════════════════════════════════════════════════════════════════════

  Move all segments from save stacks back to main stacks.

  Unlike check_restoreAll_*, these DO push a none separator when the
  save stack is exhausted. This adds the separator between instances
  that the stack format requires. Each instance's segment on the main
  stacks is delimited by none at its bottom (closest to stack bottom).

  After restoration, every instance has a none separator below its
  segment on input, workL, workR, and output stacks.
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
    ( Turing.TM2.Stmt.push DovetailStack.input (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_input) )

def step_restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workL (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workL) )

def step_restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workR (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.step_restoreAll_workR) )

def step_restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.output (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.counter_increment) )
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
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.check_iterateInstances) )
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

variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

/-- Split a none-separated stack into segments.
    The stack has newest data on top (head of list).
    Returns segments oldest-first (index 0 = oldest instance). -/
def splitSegments {α : Type u} : List (Option α) → List (List α)
  | [] => []
  | l =>
    let rec go (acc : List α) (rest : List (Option α)) : List (List α) :=
      match rest with
      | [] => [acc.reverse]
      | none :: tl => acc.reverse :: go [] tl
      | some x :: tl => go (x :: acc) tl
    let segs := match l with
      | none :: tl => go [] tl
      | _ => go [] l
    segs.reverse

/-- The config of instance i after round rounds. -/
def instanceConfig
    (gen : Generator Γw Γo Q)
    (i : ℕ) (round : ℕ) : GenConfig Γw Γo Q :=
  stepNHalt gen (initConfig gen i.testBit) (round - i)

def workRMatches
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (seg : List (Option Γw))
    (bound : ℕ) : Prop :=
  ∀ j : ℕ, j < bound →
    if h : j < seg.length then
      seg[j] = some (cfg.work (cfg.workIndex + 1 + ↑j))
    else
      cfg.work (cfg.workIndex + 1 + ↑j) = gen.blank

def workLMatches
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (seg : List (Option Γw))
    (bound : ℕ) : Prop :=
  ∀ j : ℕ, j < bound →
    if h : j < seg.length then
      seg[j] = some (cfg.work (cfg.workIndex - 1 - ↑j))
    else
      cfg.work (cfg.workIndex - 1 - ↑j) = gen.blank

/-- Quiescent invariant: the TM2 stacks correctly represent the state of
    the abstract dovetail machine at the start of a phase.

    Parameterised by:
    • gen: the generator being dovetailed
    • target: the word on the target stack (set at initialisation, never modified)
    • round: the number of completed rounds (= number of spawned instances)
    • label: the current TM2 label (check_iterateInstances or spawn_copyCounter)
    • tm2cfg: the TM2 configuration

    At round r, there are r instances. Instance i (0-indexed, 0 = oldest)
    has been stepped (r - i) times. Its abstract state is given by
    instanceConfig gen i r = stepNHalt gen (initConfig gen i.testBit) (r - i).

    The stacks encode all r instances' data with none separators between
    segments. Newest instance data is on top of each stack. -/
structure QuiescentInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (label : DovetailLabel)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop where
  label_eq : tm2cfg.l = some label
  counter : tm2cfg.stk DovetailStack.counter = (Nat.bits round).map ULift.up
  input : tm2cfg.stk DovetailStack.input =
    ((List.range round).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map (fun b => some (ULift.up b))
    )).reverse.flatten
  state : tm2cfg.stk DovetailStack.state =
    ((List.range round).map (fun i => (instanceConfig gen i round).state)).reverse
  output : tm2cfg.stk DovetailStack.output =
    ((List.range round).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten
  workR_len : (splitSegments (tm2cfg.stk DovetailStack.workR)).length = round
  workR : ∀ i (hi : i < round),
    workRMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by omega⟩)
      (round - i)
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round
  workL : ∀ i (hi : i < round),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  target_preserved : tm2cfg.stk DovetailStack.target = target
  save_empty :
    tm2cfg.stk DovetailStack.saveTarget = [] ∧
    tm2cfg.stk DovetailStack.saveCounter = [] ∧
    tm2cfg.stk DovetailStack.saveInput = [] ∧
    tm2cfg.stk DovetailStack.saveState = [] ∧
    tm2cfg.stk DovetailStack.saveWorkL = [] ∧
    tm2cfg.stk DovetailStack.saveWorkR = [] ∧
    tm2cfg.stk DovetailStack.saveOutput = []

/-- Mid-check-phase invariant: j instances have been checked (newest j),
    with their segments moved to save stacks. The remaining (round - j)
    oldest instances remain on the main stacks.

    The check phase processes instances from newest to oldest (top of stack).
    After checking j instances, the main stacks hold instances 0..round-j-1
    and the save stacks hold instances round-j..round-1.

    None of the checked instances had matching output. -/
structure CheckPhaseInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop where
  label_eq : tm2cfg.l = some DovetailLabel.check_iterateInstances
  hj : j ≤ round
  noMatch : ∀ i, round - j ≤ i → i < round →
    ¬(IsHalting gen (instanceConfig gen i round) ∧
      (instanceConfig gen i round).output.reverse = target)
  -- ═══ Main stacks: oldest round-j instances (indices 0..round-j-1) ═══
  state : tm2cfg.stk DovetailStack.state =
    ((List.range (round - j)).map
      (fun i => (instanceConfig gen i round).state)).reverse
  output : tm2cfg.stk DovetailStack.output =
    ((List.range (round - j)).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten
  input : tm2cfg.stk DovetailStack.input =
    ((List.range (round - j)).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)))).reverse.flatten
  workR_len : (splitSegments (tm2cfg.stk DovetailStack.workR)).length = round - j
  workR : ∀ i (hi : i < round - j),
    workRMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by omega⟩)
      (round - i)
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round - j
  workL : ∀ i (hi : i < round - j),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  -- ═══ Save stacks: newest j instances (indices round-j..round-1) ═══
  -- saveState: j entries. First processed = index round-1 (was on top of main).
  -- It gets pushed to saveState first, so it's at the bottom.
  -- Last processed = index round-j, on top of saveState.
  saveState : tm2cfg.stk DovetailStack.saveState =
    (List.range j).map
      (fun k => (instanceConfig gen (round - j + k) round).state)
  -- saveOutput: j segments, same indexing as saveState
  saveOutput : tm2cfg.stk DovetailStack.saveOutput =
    ((List.range j).map (fun k =>
      let i := round - j + k
      [none] ++ (instanceConfig gen i round).output.map some)).flatten
  -- saveInput: j segments
  saveInput : tm2cfg.stk DovetailStack.saveInput =
    ((List.range j).map (fun k =>
      let i := round - j + k
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)))).flatten
  -- saveWorkR/saveWorkL: j segments
  saveWorkR_len : (splitSegments (tm2cfg.stk DovetailStack.saveWorkR)).length = j
  saveWorkR : ∀ k (hk : k < j),
    workRMatches gen (instanceConfig gen (round - j + k) round)
      ((splitSegments (tm2cfg.stk DovetailStack.saveWorkR)).get ⟨k, by omega⟩)
      (round - (round - j + k))
  saveWorkL_len : (splitSegments (tm2cfg.stk DovetailStack.saveWorkL)).length = j
  saveWorkL : ∀ k (hk : k < j),
    workLMatches gen (instanceConfig gen (round - j + k) round)
      ((splitSegments (tm2cfg.stk DovetailStack.saveWorkL)).get ⟨k, by omega⟩)
      (round - (round - j + k))
  -- ═══ Preserved ═══
  counter : tm2cfg.stk DovetailStack.counter = (Nat.bits round).map ULift.up
  target_preserved : tm2cfg.stk DovetailStack.target = target
  saveTarget_empty : tm2cfg.stk DovetailStack.saveTarget = []
  saveCounter_empty : tm2cfg.stk DovetailStack.saveCounter = []

set_option linter.unusedSectionVars false
lemma quiescentInvariant_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    QuiescentInvariant gen target 0 DovetailLabel.check_iterateInstances (dovetailInit target) where
  label_eq := by
    rfl
  counter := by
    simp [dovetailInit, Turing.TM2.init, Function.update]
  input := by
    rfl
  state := by
    simp [dovetailInit, Turing.TM2.init, Function.update]
  output := by
    rfl
  workR_len := by
    simp [splitSegments, dovetailInit, Turing.TM2.init]
  workR := by
    intro i hi
    omega
  workL_len := by simp [splitSegments, dovetailInit, Turing.TM2.init]
  workL := by
    intro i hi
    omega
  target_preserved := by
    rfl
  save_empty := by
    simp [dovetailInit, Turing.TM2.init]

/-- The abstract DovetailState is "in correspondence" with a TM2 config
    when the QuiescentInvariant holds at check_iterateInstances.
    This is the bisimulation relation between the abstract dovetail machine
    and the concrete TM2 implementation. -/
def InCorrespondence
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop :=
  QuiescentInvariant gen target ds.instances.length DovetailLabel.check_iterateInstances tm2cfg

/-- The initial configs are in correspondence. -/
lemma inCorrespondence_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    InCorrespondence gen target initDovetailState (dovetailInit target) := by
  exact quiescentInvariant_init gen target

/-- From check_iterateInstances with j instances already processed and no match among them,
    processing one more non-matching instance advances to j+1. -/
lemma checkPhase_advance_no_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hNoMatch_j : ¬(IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
      (instanceConfig gen (round - 1 - j) round).output.reverse = target)) :
    ∃ tm2cfg',
      CheckPhaseInvariant gen target round (j + 1) tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- If check_compareOutput is entered with matching output on top of the stacks,
    the TM2 halts. The output stack has the output symbols reversed
    (last symbol on top) followed by a separator or end. -/
lemma check_compareOutput_halts_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hLabel : tm2cfg.l = some DovetailLabel.check_compareOutput)
    (hTarget : tm2cfg.stk DovetailStack.target = target)
    -- Output stack: reversed output on top, then none or empty
    (hOutput : ∃ rest : List (Option Γo),
      tm2cfg.stk DovetailStack.output = target.reverse.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none))
    (hSaveTarget : tm2cfg.stk DovetailStack.saveTarget = [])
    (hSaveOutput : tm2cfg.stk DovetailStack.saveOutput = []) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- From check_iterateInstances with j instances already processed, if instance j matches,
    the TM2 reaches a halted config. -/
lemma checkPhase_halt_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hMatch_j : IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
      (instanceConfig gen (round - 1 - j) round).output.reverse = target) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨hHalt_j, hOut_j⟩ := hMatch_j
  let idx := round - 1 - j
  let cfg := instanceConfig gen idx round
  -- Step 1: check_iterateInstances pops state, goes to check_testHalting
  -- The top of state stack is (instanceConfig gen idx round).state
  -- Step 2: check_testHalting peeks input, peeks workR, applies delta, finds halting
  -- Step 3: pushes state back, goes to check_compareOutput
  -- These are a bounded number of TM2 steps from tm2cfg to some tm2cfg_co
  -- at label check_compareOutput
  have hSteps : ∃ tm2cfg_co : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q),
      tm2cfg_co.l = some DovetailLabel.check_compareOutput ∧
      tm2cfg_co.stk DovetailStack.target = target ∧
      (∃ rest : List (Option Γo), tm2cfg_co.stk DovetailStack.output =
        cfg.output.map some ++ rest) ∧
      tm2cfg_co.stk DovetailStack.saveTarget = [] ∧
      tm2cfg_co.stk DovetailStack.saveOutput = [] ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_co := by
    sorry
  obtain ⟨tm2cfg_co, hLabel_co, hTarget_co, ⟨rest, hOutput_co⟩,
    hSaveTarget_co, hSaveOutput_co, hReach_co⟩ := hSteps
  -- Step 4: check_compareOutput compares and halts
  -- output on stack is cfg.output.map some ++ rest (newest output symbol on top)
  -- target on stack is target
  -- cfg.output.reverse = target (from hOut_j)
  -- So the comparison succeeds
  have hOutEq : cfg.output = target.reverse :=
    List.reverse_injective (by rw [List.reverse_reverse]; exact hOut_j)
  obtain ⟨tm2cfg', hHalt', hReach'⟩ := check_compareOutput_halts_on_match gen
    target tm2cfg_co
    hLabel_co hTarget_co
    ⟨rest, by rw [hOutput_co, hOutEq], sorry⟩
    hSaveTarget_co hSaveOutput_co
  exact ⟨tm2cfg', hHalt', Relation.ReflTransGen.trans hReach_co hReach'⟩

/-- A QuiescentInvariant at check_iterateInstances gives a CheckPhaseInvariant at j=0. -/
lemma quiescent_to_checkPhase
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round DovetailLabel.check_iterateInstances tm2cfg) :
    CheckPhaseInvariant gen target round 0 tm2cfg where
  label_eq := hInv.label_eq
  hj := Nat.zero_le _
  noMatch := by intro i hi; omega
  state := by simp [hInv.state]
  output := by simp [hInv.output]
  input := by simp [hInv.input]
  workR_len := by simp [hInv.workR_len]
  workR := hInv.workR
  workL_len := by simp [hInv.workL_len]
  workL := hInv.workL
  saveState := by
    simp only [tsub_zero, List.range_zero, List.map_nil]
    exact hInv.save_empty.2.2.2.1
  saveOutput := by
    simp only [tsub_zero, List.cons_append, List.nil_append, List.range_zero,
      List.map_nil, List.flatten_nil]
    exact hInv.save_empty.2.2.2.2.2.2
  saveInput := by
    simp only [tsub_zero, List.map_drop, List.cons_append, List.nil_append,
      List.range_zero, List.map_nil, List.flatten_nil]
    exact hInv.save_empty.2.2.1
  saveWorkR_len := by
    simp only [splitSegments, List.length_eq_zero_iff]
    have h := hInv.save_empty.2.2.2.2.2.1
    rw [h]
  saveWorkR := by intro k hk; omega
  saveWorkL_len := by
    simp only [splitSegments, List.length_eq_zero_iff]
    have h := hInv.save_empty.2.2.2.2.1
    rw [h]
  saveWorkL := by intro k hk; omega
  counter := hInv.counter
  target_preserved := hInv.target_preserved
  saveTarget_empty := hInv.save_empty.1
  saveCounter_empty := hInv.save_empty.2.1

/-- If in correspondence and some instance has halting output matching
    the target (reversed, due to stack ordering), the TM2 reaches a
    halted configuration. This is the key lemma for the backward direction:
    DovetailRecognises → TM2 halts. -/
lemma inCorrespondence_halt
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hCorr : InCorrespondence gen target ds tm2cfg)
    (hMatch : ∃ i, i < ds.instances.length ∧
      IsHalting gen (instanceConfig gen i ds.instances.length) ∧
      (instanceConfig gen i ds.instances.length).output.reverse = target) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨k, hk_lt, hk_halt, hk_out⟩ := hMatch
  let round := ds.instances.length
  have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
  suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q)),
      round - j = d →
      j ≤ round →
      CheckPhaseInvariant gen target round j tm2cfg_j →
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
      (∃ i, i < round - j ∧
        IsHalting gen (instanceConfig gen i round) ∧
        (instanceConfig gen i round).output.reverse = target) →
      ∃ tm2cfg',
        tm2cfg'.l = none ∧
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' by
    exact this round 0 tm2cfg (by omega) (Nat.zero_le _) hCheck₀
      Relation.ReflTransGen.refl ⟨k, by omega, hk_halt, hk_out⟩
  intro d
  induction d with
  | zero =>
    intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, _, _⟩
    omega
  | succ d ih =>
    intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, hi_halt, hi_out⟩
    -- The next instance to check is round - 1 - j
    by_cases hMatch_j : IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
        (instanceConfig gen (round - 1 - j) round).output.reverse = target
    · have hj_lt : j < round := by omega
      obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
        checkPhase_halt_on_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
      exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_j h_reaches'⟩
    · have hj_lt : j < round := by omega
      obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
        checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
      have hi_ne : i ≠ round - 1 - j := by
        intro heq; rw [heq] at hi_halt hi_out; exact hMatch_j ⟨hi_halt, hi_out⟩
      exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
        (Relation.ReflTransGen.trans hReach_j hReach_next)
        ⟨i, by omega, hi_halt, hi_out⟩

/-- From CheckPhaseInvariant with all instances checked (j = round) and no match,
    restoring save stacks reaches spawn_copyCounter with QuiescentInvariant. -/
lemma checkPhase_complete_to_pushNewConfig
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round round tm2cfg) :
    ∃ tm2cfg',
      QuiescentInvariant gen target round DovetailLabel.spawn_copyCounter tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- From spawn_copyCounter, spawn a new instance and step all,
    reaching check_iterateInstances at round+1. -/
lemma pushNewConfig_step_to_next_check_iterateInstances
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round DovetailLabel.spawn_copyCounter tm2cfg) :
    ∃ tm2cfg',
      QuiescentInvariant gen target (round + 1) DovetailLabel.check_iterateInstances tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- If in correspondence and no instance matches, one abstract dovetailStep
    corresponds to finitely many TM2 steps, reaching a new correspondence.
    This is the simulation lemma: one abstract round = one concrete round. -/
lemma inCorrespondence_step
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hCorr : InCorrespondence gen target ds tm2cfg)
    (hNoMatch : ∀ i, i < ds.instances.length →
      ¬(IsHalting gen (instanceConfig gen i ds.instances.length) ∧
        (instanceConfig gen i ds.instances.length).output.reverse = target)) :
    ∃ tm2cfg',
      InCorrespondence gen target (dovetailStep gen ds) tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  let round := ds.instances.length
  -- Phase 1: Check all instances, find no match, advance to j = round
  have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
  have hCheckAll : ∃ tm2cfg_check,
      CheckPhaseInvariant gen target round round tm2cfg_check ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check := by
    suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
          DovetailLabel (DovetailSigma Γw Γo Q)),
        round - j = d →
        j ≤ round →
        CheckPhaseInvariant gen target round j tm2cfg_j →
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
        ∃ tm2cfg_check,
          CheckPhaseInvariant gen target round round tm2cfg_check ∧
          Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check by
      exact this round 0 tm2cfg rfl (Nat.zero_le _) hCheck₀ Relation.ReflTransGen.refl
    intro d
    induction d with
    | zero =>
      intro j tm2cfg_j hd hj hInv_j hReach_j
      have : j = round := by omega
      subst this
      exact ⟨tm2cfg_j, hInv_j, hReach_j⟩
    | succ d ih =>
      intro j tm2cfg_j hd hj hInv_j hReach_j
      have hj_lt : j < round := by omega
      -- Instance round-1-j doesn't match (from hNoMatch)
      have hNoMatch_j : ¬(IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
          (instanceConfig gen (round - 1 - j) round).output.reverse = target) :=
        hNoMatch (round - 1 - j) (by omega)
      obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
        checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hNoMatch_j
      exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
        (Relation.ReflTransGen.trans hReach_j hReach_next)
  -- Phase 2: From CheckPhaseInvariant at j=round, restore to pushNewConfig
  obtain ⟨tm2cfg_check, hInv_check, hReach_check⟩ := hCheckAll
  obtain ⟨tm2cfg_push, hInv_push, hReach_push⟩ :=
    checkPhase_complete_to_pushNewConfig gen target round tm2cfg_check hInv_check
  -- Phase 3: From pushNewConfig, spawn + step + restore + increment to next check_iterateInstances
  obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
    pushNewConfig_step_to_next_check_iterateInstances gen target round tm2cfg_push hInv_push
  -- Connect everything
  refine ⟨tm2cfg_next, ?_, ?_⟩
  · -- InCorrespondence gen target (dovetailStep gen ds) tm2cfg_next
    -- This is QuiescentInvariant gen target (round+1) check_iterateInstances tm2cfg_next
    -- which is hInv_next, but we need to show round+1 = (dovetailStep gen ds).instances.length
    change QuiescentInvariant gen target (dovetailStep gen ds).instances.length
      DovetailLabel.check_iterateInstances tm2cfg_next
    rw [show (dovetailStep gen ds).instances.length = round + 1 from by
      simp [dovetailStep, round]]
    exact hInv_next
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans hReach_check hReach_push) hReach_next

lemma dovetailTM2_halts_implies_DovetailRecognises
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom →
    DovetailRecognises gen w.reverse := by
  -- One idea is to prove this by contrapositive.
  sorry

/-- Backward: if DovetailRecognises, then the TM2 halts. -/
lemma DovetailRecognises_implies_dovetailTM2_halts
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    DovetailRecognises gen w.reverse →
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom := by
  intro ⟨n, i, cfg, h_inst, h_halt, h_out⟩
  suffices ∃ tm2cfg' : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q),
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
        (dovetailInit w) tm2cfg' by
    obtain ⟨tm2cfg', h_halt', h_reaches⟩ := this
    rw [Turing.TM2.eval, Part.dom_iff_mem]
    have h_halt_step : Turing.TM2.step (dovetailMachine gen) tm2cfg' = none := by
      cases tm2cfg'; simp_all [Turing.TM2.step]
    exact ⟨tm2cfg'.stk DovetailStack.target,
      Part.mem_map _ (Turing.mem_eval.mpr ⟨h_reaches, h_halt_step⟩)⟩
  suffices ∀ r,
      ∃ (tm2cfg_r : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
            DovetailLabel (DovetailSigma Γw Γo Q)),
        (tm2cfg_r.l = none ∨
         InCorrespondence gen w
           ((dovetailStep gen)^[r] initDovetailState) tm2cfg_r) ∧
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
          (dovetailInit w) tm2cfg_r by
    obtain ⟨tm2cfg_n, hAlt, hReach_n⟩ := this n
    rcases hAlt with h_halt' | hCorr_n
    · exact ⟨tm2cfg_n, h_halt', hReach_n⟩
    · have hi : i < n := by
        by_contra h; push_neg at h
        exact absurd h_inst (by
          rw [List.getElem?_eq_none (by rw [instances_length_after_steps]; omega)]
          exact Option.some_ne_none _ ∘ Eq.symm)
      have hMatch : ∃ j,
          j < ((dovetailStep gen)^[n] initDovetailState).instances.length ∧
          IsHalting gen (instanceConfig gen j
            ((dovetailStep gen)^[n] initDovetailState).instances.length) ∧
          (instanceConfig gen j
            ((dovetailStep gen)^[n] initDovetailState).instances.length).output.reverse = w := by
        rw [instances_length_after_steps]
        refine ⟨i, hi, ?_⟩
        rw [instance_config_after_steps gen n i hi] at h_inst
        have h_eq := Option.some.inj h_inst
        rw [← h_eq] at h_halt h_out
        exact ⟨h_halt, by simp only [instanceConfig]; rw [h_out, List.reverse_reverse]⟩
      obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
        inCorrespondence_halt gen w _ tm2cfg_n hCorr_n hMatch
      exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_n h_reaches'⟩
  intro r
  induction r with
  | zero =>
    exact ⟨dovetailInit w, Or.inr (inCorrespondence_init gen w),
      Relation.ReflTransGen.refl⟩
  | succ r ih =>
    obtain ⟨tm2cfg_r, hAlt_r, hReach_r⟩ := ih
    rcases hAlt_r with h_halt_r | hCorr_r
    · exact ⟨tm2cfg_r, Or.inl h_halt_r, hReach_r⟩
    · by_cases hMatch_r : ∃ j,
          j < ((dovetailStep gen)^[r] initDovetailState).instances.length ∧
          IsHalting gen (instanceConfig gen j
            ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
          (instanceConfig gen j
            ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse = w
      · obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
          inCorrespondence_halt gen w _ tm2cfg_r hCorr_r hMatch_r
        exact ⟨tm2cfg', Or.inl h_halt', Relation.ReflTransGen.trans hReach_r h_reaches'⟩
      · push_neg at hMatch_r
        have hNoMatch : ∀ j,
            j < ((dovetailStep gen)^[r] initDovetailState).instances.length →
            ¬(IsHalting gen (instanceConfig gen j
                ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
              (instanceConfig gen j
                ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse
                = w) := by
          intro j hj ⟨hHalt, hOut⟩
          exact hMatch_r j hj hHalt hOut
        obtain ⟨tm2cfg_next, hCorr_next, hReach_next⟩ :=
          inCorrespondence_step gen w _ tm2cfg_r hCorr_r hNoMatch
        rw [show (dovetailStep gen)^[r + 1] initDovetailState =
            dovetailStep gen ((dovetailStep gen)^[r] initDovetailState) from
          by rw [Function.iterate_succ', Function.comp_apply]]
        exact ⟨tm2cfg_next, Or.inr hCorr_next,
          Relation.ReflTransGen.trans hReach_r hReach_next⟩

/-- The dovetail TM2 halts on input w iff DovetailRecognises gen w.reverse. -/
theorem dovetailTM2_halts_iff_DovetailRecognises
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom ↔
    DovetailRecognises gen w.reverse :=
  ⟨dovetailTM2_halts_implies_DovetailRecognises gen w,
   DovetailRecognises_implies_dovetailTM2_halts gen w⟩

set_option linter.unusedSectionVars true
end Dovetailing

-- The dovetail   TM2 halts on input `target` iff `target` is in the generated language.
theorem dovetailMachine_recognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target target.reverse).Dom ↔
    target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
  rw [dovetailTM2_halts_iff_DovetailRecognises]
  simp only [List.reverse_reverse]
  rw [DovetailRecognises_iff_Computes]
  simp only [generatedLanguage, Set.mem_setOf_eq]

lemma every_generable_language_is_tm2_recognisable
    {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ generableLanguages) :
    L ∈ languagesRecognisedByTM2s := by
  obtain ⟨Γw, Q, hΓwfinenum, hQdec, gen, S_gen, hS_gen, hgen⟩ := hL
  haveI : DecidableEq Q := hQdec
  let gen' := @Generator.restrictToSupport Γw Γ Q hΓwfinenum _ _ gen S_gen hS_gen
  haveI : Fintype ↥S_gen := inferInstance
  haveI : DecidableEq ↥S_gen := inferInstance
  haveI : FinEnum ↥S_gen := FinEnum.ofList (Finset.univ.val.toList) (by simp)
  haveI : Inhabited ↥S_gen := ⟨gen'.init⟩
  haveI : ∀ k, Inhabited (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : ∀ k, Fintype (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : ∀ k, DecidableEq (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : Inhabited Γw := ⟨gen.blank⟩
  refine ⟨
    DovetailStack,
    inferInstance,
    inferInstance,
    inferInstance,
    stackAlphabet Γw Γ ↥S_gen,
    inferInstance,
    inferInstance,
    inferInstance,
    rfl,
    DovetailLabel,
    inferInstance,
    inferInstance,
    DovetailSigma Γw Γ ↥S_gen,
    inferInstance,
    inferInstance,
    dovetailMachine gen',
    Finset.univ,
    ⟨Finset.mem_univ _, fun q _ => by
      cases q <;> simp only [dovetailMachine,
        check_iterateInstances, check_testHalting, check_compareOutput, check_compareOutput_restoreTarget, check_compareOutput_restoreOutput,
        check_saveInstance_state, check_saveInstance_input,
        check_saveInstance_workL, check_saveInstance_workR,
        check_saveInstance_output,
        check_restoreAll_state, check_restoreAll_input,
        check_restoreAll_workL, check_restoreAll_workR,
        check_restoreAll_output,
        spawn_copyCounter, spawn_restoreAndPush,
        step_iterateInstances, step_peekInput, step_peekWorkR, step_applyTransition, step_consumeInput,
        step_moveWorkHead,
        step_saveInstance_state, step_saveInstance_input, step_saveInstance_workL, step_saveInstance_workR,
        step_saveInstance_output, step_restoreAll_state, step_restoreAll_input,
        step_restoreAll_workL, step_restoreAll_workR, step_restoreAll_output,
        counter_increment, counter_increment_loop, counter_increment_restore,
        Turing.TM2.SupportsStmt] <;>
      simp (config := { decide := true })⟩,
    ?_⟩
  subst hgen
  ext input
  simp only [Set.mem_setOf_eq]
  have lang_eq : generatedLanguage gen S_gen hS_gen =
      generatedLanguage gen' Finset.univ (generator_supports_univ gen') := by
    ext w
    simp only [generatedLanguage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes gen S_gen hS_gen h⟩
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes_lift gen S_gen hS_gen h⟩
  rw [lang_eq]
  exact (dovetailMachine_recognises gen' input).symm

end RandomisedGeneration
