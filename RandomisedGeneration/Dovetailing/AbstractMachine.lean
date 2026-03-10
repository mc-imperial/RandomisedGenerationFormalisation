import Mathlib
import RandomisedGeneration.Generator

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

structure DovetailState where
  instances : List (GenConfig Γw Γo Q)
  nextInput : ℕ

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

end Dovetailing

end RandomisedGeneration
