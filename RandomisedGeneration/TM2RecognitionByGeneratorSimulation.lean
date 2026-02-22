import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Fintype Γw]
variable [Inhabited Γo] [FinEnum Γo]

structure DovetailState where
  instances : List (Option (GenConfig Γw Γo Q))
  nextInput : ℕ

def dovetailStep
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { instances := ds.instances.map (fun cfg => cfg.bind (step gen))
                 ++ [some (initConfig gen (Nat.testBit ds.nextInput))]
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
    insts[i]? = some (some cfg) ∧
    IsHalting gen cfg ∧
    cfg.output = w

-- The "already stepped" prefix
def steppedPrefix
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (Option (GenConfig Γw Γo Q)) :=
  (ds.instances.take k).map (·.bind (step gen))

-- The "not yet stepped" suffix
def pendingSuffix
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (Option (GenConfig Γw Γo Q)) :=
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
    { ds with instances := ds.instances.map (·.bind (step gen)) } := by
  simp [midRoundState, steppedPrefix, pendingSuffix, List.take_length, List.drop_length]

-- Advancing the frontier by one
lemma midRoundState_succ
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ)
  (hk : k < ds.instances.length) :
  midRoundState gen ds (k + 1) =
  { ds with instances :=
      (ds.instances.take k).map (·.bind (step gen))
      ++
      [ (ds.instances.get ⟨k, hk⟩).bind (step gen) ]
      ++
      ds.instances.drop (k + 1) } := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  congr 1
  rw [List.take_add_one, List.map_append]
  simp [List.getElem?_eq_getElem hk]

-- The full dovetailStep decomposes into midRoundState at length, then spawn
lemma dovetailStep_eq_spawn_of_midRound
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  dovetailStep gen ds =
    { instances :=
        (midRoundState gen ds ds.instances.length).instances ++
          [some (initConfig gen (Nat.testBit ds.nextInput))]
      nextInput := ds.nextInput + 1 } := by
  simp [dovetailStep, midRoundState_length]

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
    (ds.instances[i]?).map (·.bind (step gen)) := by
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
  have : (List.map (·.bind (step gen)) (ds.instances.take k) ++
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
    some (stepN gen (some (initConfig gen i.testBit)) (n - i - 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp only [List.getElem?_append]
    by_cases hi' : i < n
    · have ih' := ih hi'
      simp only [List.length_map]
      rw [if_pos (by
        rw [instances_length_after_steps]
        exact hi')]
      rw [List.getElem?_map, ih']
      simp only [Option.map_some]
      rw [← stepN_succ]
      congr 2
      omega
    · have hi'' : i = n := by omega
      subst hi''
      simp only [List.length_map]
      rw [instances_length_after_steps, if_neg (by omega)]
      rw [show i - i = 0 by omega]
      simp only [List.length_cons, List.length_nil, zero_add,
        zero_lt_one, getElem?_pos, List.getElem_cons_zero,
    add_tsub_cancel_left, tsub_self, stepN_zero, Option.some.injEq]
      rw [nextInput_after_steps]

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
      have hdom := of_getElem?_eq_some h_inst
      simp only [hlen] at hdom
      exact hdom
    have h_stepN := instance_config_after_steps gen n i hi
    rw [h_inst] at h_stepN
    have h_eq : stepN gen (some (initConfig gen (Nat.testBit i))) (n - i - 1) = some cfg :=
      Option.some_inj.mp h_stepN.symm
    rw [stepN_eq_Steps] at h_eq
    exact Reachable.computes ⟨_, h_eq⟩ h_halt
  · -- Backward: ∃ m, Computes → DovetailRecognises
    intro ⟨f, h_computes⟩
    obtain ⟨m, h_computes'⟩ := h_computes.exists_natTestBit
    obtain ⟨k, haltCfg, h_stepN, h_halt, h_out⟩ := h_computes'.to_stepN
    refine ⟨m + k + 1, m, haltCfg, ?_, h_halt, h_out⟩
    have hm : m < m + k + 1 := by omega
    have h_inst := instance_config_after_steps gen (m + k + 1) m hm
    rw [show m + k + 1 - m - 1 = k by omega] at h_inst
    rw [h_stepN] at h_inst
    exact h_inst

end Dovetailing

end RandomisedGeneration
