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

inductive DovetailStack : Type u
  | target        -- String in Γo to be recognised. Only one copy (not one per generator instance)
  | counter       -- Booleans representing the counter that should be used for the next generator
                  --   instance. Initially empty (which corresponds to a bitstream of all zeros).
  | input         -- The bitstream prefix for each generator instance, with "none" used after the
                  --   bitstream for a given instance. If the bitstream for an instance is empty
                  --   this means that the instance will read zeros forevermore.
  | state         -- A series of Q elements, one per active instance.
  | workL         -- A none-separated series of Γw elements representing what lies to the left
                  --   of the tape head for each instance.
  | workR         -- Similar but for what is to the right of the tape head for each instance.
  | output        -- A non-separated series of Γo elements indicating what has been ouptut by each
                  --   instance.
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

def stackAlphabet (Γw Γo Q : Type u)
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    DovetailStack → Type u
  -- target holds Γo elements (no separator needed, it's a single word)
  | DovetailStack.target    => Γo
  -- counter holds Bool (the binary representation of the next input number)
  | DovetailStack.counter   => ULift.{u} Bool
  -- input holds Option Bool: some b for a bit, none as separator between instances
  | DovetailStack.input     => Option (ULift.{u} Bool)
  -- state holds Q, one per instance
  | DovetailStack.state     => Q
  -- workL and workR hold Option Γw: some x for a tape symbol, none as separator
  | DovetailStack.workL     => Option Γw
  | DovetailStack.workR     => Option Γw
  -- output holds Option Γo: some x for an output symbol, none as separator
  | DovetailStack.output    => Option Γo
  -- save stacks mirror their corresponding main stacks
  | DovetailStack.saveTarget  => Γo
  | DovetailStack.saveCounter => ULift.{u} Bool
  | DovetailStack.saveInput   => Option (ULift.{u} Bool)
  | DovetailStack.saveState   => Q
  | DovetailStack.saveWorkL   => Option Γw
  | DovetailStack.saveWorkR   => Option Γw
  | DovetailStack.saveOutput  => Option Γo

-- Labels correspond to the subroutines and their internal loops
inductive DovetailLabel : Type u
  -- Phase 1: Check all instances for halting + output match
  | checkAll
  | checkOne
  | checkOutput
  | restoreTarget
  | restoreOutput
  | checkPhase_saveSegment
  | checkPhase_saveSegment_input
  | checkPhase_saveSegment_workL
  | checkPhase_saveSegment_workR
  | checkPhase_saveSegment_output
  -- Phase 2: Restore from check phase, then spawn new instance
  | checkPhase_restoreAll_state
  | checkPhase_restoreAll_input
  | checkPhase_restoreAll_workL
  | checkPhase_restoreAll_workR
  | checkPhase_restoreAll_output
  | pushNewConfig_copy_counter
  | pushNewConfig_restore_counter
  -- Phase 3: Step all instances
  | stepAll
  | stepOne
  | stepOne_workR
  | applyTransition
  | applyInputDir
  | applyWorkDir
  | saveSegment
  | saveSegment_input
  | saveSegment_workL
  | saveSegment_workR
  | saveSegment_output
  -- Phase 4: Restore from step phase, increment counter
  | restoreAll_state
  | restoreAll_input
  | restoreAll_workL
  | restoreAll_workR
  | restoreAll_output
  | incrementCounter
  | incrementCounter_loop
  | incrementCounter_restore
deriving DecidableEq, Fintype

set_option linter.style.whitespace false
set_option linter.style.longLine false
structure DovetailSigma (Γw Γo Q : Type u)
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] where

  -- ── Generator transition results ──────────────────────────────────────
  transQ    : Option Q
  transW    : Option Γw
  transIDir : InputTapeDirection
  transWDir : WorkTapeDirection
  transOut  : Option (Option Γo)
  transHalted : Bool

  -- ── Current input bit ─────────────────────────────────────────────────
  inputBit  : ULift.{u} Bool

  -- ── Scratch space for peek/pop decisions ──────────────────────────────
  peekQ     : Option Q
  peekBit   : Option (ULift.{u} Bool)
  peekInput : Option (Option (ULift.{u} Bool))
  peekWorkL : Option (Option Γw)
  peekWorkR : Option (Option Γw)
  peekOut   : Option (Option Γo)
  peekTarget : Option Γo

  -- ── Binary counter ────────────────────────────────────────────────────
  carry     : Option (ULift.{u} Bool)
set_option linter.style.whitespace true
set_option linter.style.longLine true

instance : Inhabited DovetailLabel := ⟨DovetailLabel.checkAll⟩

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

  Flow: checkAll → checkOne → (if halting) checkOutput → restoreTarget →
        restoreOutput → checkPhase_saveSegment → ... → checkAll
        (if not halting) checkPhase_saveSegment → ... → checkAll
  When all instances checked: checkAll → checkPhase_restoreAll_state → ...
        → pushNewConfig_copy_counter
══════════════════════════════════════════════════════════════════════════════
-/

-- Peek state stack: if empty, all checked → restore and proceed to spawn phase
def checkAll {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkOne) )

-- Peek input and workR to determine if this instance is halting
def checkOne {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with
    inputBit  := match i with
                 | some (some b) => b
                 | _             => ULift.up false
    peekInput := i })
  <| Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with
    transW    := match w with
                 | some (some x) => some x
                 | _             => some gen.blank
    peekWorkR := w })
  <| Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
  <| Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
    ( -- halting: push state back and check output
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkOutput) )
    ( -- not halting: push state back and save segments to move to next instance
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment) )

-- Compare output of halting instance against target
def checkOutput {Γw Γo Q : Type u}
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
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) ) )
    ( Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
            | none      => true
            | some none => true
            | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) )
        ( Turing.TM2.Stmt.branch (fun σ => match σ.peekTarget, σ.peekOut with
              | some t, some (some o) => decide (t = o)
              | _, _                  => false)
            ( Turing.TM2.Stmt.pop DovetailStack.target (fun σ _ => σ)
              <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
              <| Turing.TM2.Stmt.push DovetailStack.saveTarget
                (fun σ => σ.peekTarget.getD default)
              <| Turing.TM2.Stmt.push DovetailStack.saveOutput
                (fun σ => σ.peekOut.getD none)
              <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkOutput) )
            ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) ) ) )

def restoreTarget {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveTarget (fun σ t => { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreOutput) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveTarget (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.target
        (fun σ => σ.peekTarget.getD default)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) )

def restoreOutput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreOutput) )

-- Check phase save segment: save this instance's segments then return to checkAll
def checkPhase_saveSegment {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.pop DovetailStack.state (fun σ q => { σ with peekQ := q })
  <| Turing.TM2.Stmt.push DovetailStack.saveState
    (fun σ => σ.peekQ.getD gen.init)
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_input)

def checkPhase_saveSegment_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workL) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_input) ) )

def checkPhase_saveSegment_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workR) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workL) ) )

def checkPhase_saveSegment_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_output) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_workR) ) )

def checkPhase_saveSegment_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkAll) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkAll) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_saveSegment_output) ) )

-- Check phase restore: restore all saved segments then proceed to spawn
def checkPhase_restoreAll_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveState (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_input) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveState (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_state) )

def checkPhase_restoreAll_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveInput (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_input) )

def checkPhase_restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_workL) )

def checkPhase_restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_workR) )

def checkPhase_restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_copy_counter) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkPhase_restoreAll_output) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 2: Spawn a new instance
══════════════════════════════════════════════════════════════════════════════
-/

def pushNewConfig_copy_counter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_restore_counter) )
    ( Turing.TM2.Stmt.pop DovetailStack.counter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.saveCounter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_copy_counter) )

def pushNewConfig_restore_counter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.state (fun _ => gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.counter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekBit)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_restore_counter) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 3: Step all instances
══════════════════════════════════════════════════════════════════════════════
-/

def stepAll {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_state) )
    ( Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepOne) )

def stepOne {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with
    inputBit  := match i with
                 | some (some b) => b
                 | _             => ULift.up false
    peekInput := i })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepOne_workR)

def stepOne_workR {Γw Γo Q : Type u}
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
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyTransition) )
    ( Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyTransition) )

-- For both halted and running: push state and workR back, then handle rest
def applyTransition {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
    ( -- instance halted: push state and work symbol back, go to saveSegment
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.transW.map some |>.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
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
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyInputDir) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyInputDir) ) )

def applyInputDir {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => match σ.transIDir, σ.peekInput with
      | InputTapeDirection.R, some (some _) => true
      | _, _                                => false)
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyWorkDir) )
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyWorkDir) )

def applyWorkDir {Γw Γo Q : Type u}
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
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
        ( Turing.TM2.Stmt.push DovetailStack.workR
            (fun _ => some gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )
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
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
          ( Turing.TM2.Stmt.push DovetailStack.workL
              (fun _ => some gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )
      ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )

-- Step phase save segment: save this instance's segments then return to stepAll
def saveSegment {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.pop DovetailStack.state (fun σ q => { σ with peekQ := q })
  <| Turing.TM2.Stmt.push DovetailStack.saveState
    (fun σ => σ.peekQ.getD gen.init)
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_input)

def saveSegment_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_input) ) )

def saveSegment_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) ) )

def saveSegment_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) ) )

def saveSegment_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
    ( Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) ) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 4: Restore from step phase, increment counter
══════════════════════════════════════════════════════════════════════════════
-/

def restoreAll_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveState (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_input) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveState (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_state) )

def restoreAll_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveInput (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.input (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_input) )

def restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workL (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workL) )

def restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workR (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workR) )

def restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.output (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_output) )

/-
══════════════════════════════════════════════════════════════════════════════
  Phase 5: Increment counter
══════════════════════════════════════════════════════════════════════════════
-/

def incrementCounter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.load (fun σ => { σ with carry := some (ULift.up true) })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_loop)

def incrementCounter_loop {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.branch (fun σ => match σ.carry with
          | some b => ULift.down b
          | none   => false)
        ( Turing.TM2.Stmt.push DovetailStack.counter (fun _ => ULift.up true)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) ) )
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
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_loop) )

def incrementCounter_restore {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkAll) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.counter
          (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) )

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
  | DovetailLabel.checkAll => checkAll
  | DovetailLabel.checkOne => checkOne gen
  | DovetailLabel.checkOutput => checkOutput
  | DovetailLabel.restoreTarget => restoreTarget
  | DovetailLabel.restoreOutput => restoreOutput
  | DovetailLabel.checkPhase_saveSegment => checkPhase_saveSegment gen
  | DovetailLabel.checkPhase_saveSegment_input => checkPhase_saveSegment_input
  | DovetailLabel.checkPhase_saveSegment_workL => checkPhase_saveSegment_workL
  | DovetailLabel.checkPhase_saveSegment_workR => checkPhase_saveSegment_workR
  | DovetailLabel.checkPhase_saveSegment_output => checkPhase_saveSegment_output
  | DovetailLabel.checkPhase_restoreAll_state => checkPhase_restoreAll_state gen
  | DovetailLabel.checkPhase_restoreAll_input => checkPhase_restoreAll_input
  | DovetailLabel.checkPhase_restoreAll_workL => checkPhase_restoreAll_workL
  | DovetailLabel.checkPhase_restoreAll_workR => checkPhase_restoreAll_workR
  | DovetailLabel.checkPhase_restoreAll_output => checkPhase_restoreAll_output
  -- Phase 2: Spawn
  | DovetailLabel.pushNewConfig_copy_counter => pushNewConfig_copy_counter
  | DovetailLabel.pushNewConfig_restore_counter => pushNewConfig_restore_counter gen
  -- Phase 3: Step
  | DovetailLabel.stepAll => stepAll
  | DovetailLabel.stepOne => stepOne
  | DovetailLabel.stepOne_workR => stepOne_workR gen
  | DovetailLabel.applyTransition => applyTransition gen
  | DovetailLabel.applyInputDir => applyInputDir
  | DovetailLabel.applyWorkDir => applyWorkDir gen
  | DovetailLabel.saveSegment => saveSegment gen
  | DovetailLabel.saveSegment_input => saveSegment_input
  | DovetailLabel.saveSegment_workL => saveSegment_workL
  | DovetailLabel.saveSegment_workR => saveSegment_workR
  | DovetailLabel.saveSegment_output => saveSegment_output
  -- Phase 4: Restore + increment
  | DovetailLabel.restoreAll_state => restoreAll_state gen
  | DovetailLabel.restoreAll_input => restoreAll_input
  | DovetailLabel.restoreAll_workL => restoreAll_workL
  | DovetailLabel.restoreAll_workR => restoreAll_workR
  | DovetailLabel.restoreAll_output => restoreAll_output
  | DovetailLabel.incrementCounter => incrementCounter
  | DovetailLabel.incrementCounter_loop => incrementCounter_loop
  | DovetailLabel.incrementCounter_restore => incrementCounter_restore

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

set_option linter.unusedSectionVars false
lemma quiescentInvariant_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    QuiescentInvariant gen target 0 DovetailLabel.checkAll (dovetailInit target) where
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

/-- A DovetailState corresponds to a TM2 config via the invariant. -/
def InCorrespondence
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop :=
  QuiescentInvariant gen target ds.instances.length DovetailLabel.checkAll tm2cfg

/-- The initial configs are in correspondence. -/
lemma inCorrespondence_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    InCorrespondence gen target initDovetailState (dovetailInit target) := by
  exact quiescentInvariant_init gen target

/-- If in correspondence and some instance halts with matching output,
    the TM2 reaches a halted config. -/
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
  sorry

/-- If in correspondence and no instance halts with matching output,
    one dovetailStep and finitely many TM2 steps lead to new configs
    in correspondence. -/
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
  sorry

/-- The dovetail TM2 halts on input w iff DovetailRecognises gen w.reverse. -/
theorem dovetailTM2_halts_iff_DovetailRecognises
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom ↔
    DovetailRecognises gen w.reverse := by
  constructor
  · -- Forward: TM2 halts → DovetailRecognises
    sorry
  · -- Backward: DovetailRecognises → TM2 halts
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
    -- We show: for any r, either we halt by round r, or we reach round r in correspondence.
    -- Since we know a match exists at round n, we must halt by round n.
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
      · -- Already halted at or before round n
        exact ⟨tm2cfg_n, h_halt', hReach_n⟩
      · -- Reached round n in correspondence; now there's a match
        have hi : i < n := by
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
    -- Prove by induction: at each round, either halted or in correspondence
    intro r
    induction r with
    | zero =>
      exact ⟨dovetailInit w, Or.inr (inCorrespondence_init gen w),
        Relation.ReflTransGen.refl⟩
    | succ r ih =>
      obtain ⟨tm2cfg_r, hAlt_r, hReach_r⟩ := ih
      rcases hAlt_r with h_halt_r | hCorr_r
      · -- Already halted: propagate
        exact ⟨tm2cfg_r, Or.inl h_halt_r, hReach_r⟩
      · -- In correspondence at round r: check for match
        by_cases hMatch_r : ∃ j,
            j < ((dovetailStep gen)^[r] initDovetailState).instances.length ∧
            IsHalting gen (instanceConfig gen j
              ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
            (instanceConfig gen j
              ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse = w
        · -- Match at round r: halt
          obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
            inCorrespondence_halt gen w _ tm2cfg_r hCorr_r hMatch_r
          exact ⟨tm2cfg', Or.inl h_halt', Relation.ReflTransGen.trans hReach_r h_reaches'⟩
        · -- No match at round r: step forward
          push_neg at hMatch_r
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
        checkAll, checkOne, checkOutput, restoreTarget, restoreOutput,
        checkPhase_saveSegment, checkPhase_saveSegment_input,
        checkPhase_saveSegment_workL, checkPhase_saveSegment_workR,
        checkPhase_saveSegment_output,
        checkPhase_restoreAll_state, checkPhase_restoreAll_input,
        checkPhase_restoreAll_workL, checkPhase_restoreAll_workR,
        checkPhase_restoreAll_output,
        pushNewConfig_copy_counter, pushNewConfig_restore_counter,
        stepAll, stepOne, stepOne_workR, applyTransition, applyInputDir,
        applyWorkDir,
        saveSegment, saveSegment_input, saveSegment_workL, saveSegment_workR,
        saveSegment_output, restoreAll_state, restoreAll_input,
        restoreAll_workL, restoreAll_workR, restoreAll_output,
        incrementCounter, incrementCounter_loop, incrementCounter_restore,
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
