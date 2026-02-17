import Mathlib

namespace RandomisedGeneration

inductive WorkTapeDirection
  | L     -- move left
  | R     -- move right
  | N     -- stay / no move

instance : Coe WorkTapeDirection ℤ :=
⟨fun
  | WorkTapeDirection.L => -1
  | WorkTapeDirection.N => 0
  | WorkTapeDirection.R => 1⟩

inductive InputTapeDirection
  | R     -- move right
  | N     -- stay / no move

instance : Coe InputTapeDirection ℕ :=
⟨fun
  | InputTapeDirection.N => 0
  | InputTapeDirection.R => 1⟩

-- Sigma is the working tape alphabet.
-- Γ is the output tape alphabet.
-- Q is the set of states.
structure Generator (Γw Γo Q : Type u)
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
where
  init : Q -- Initial state
  blank : Γw -- Blank symbol for the working tape
  -- A transition is determined by:
  -- - the current state
  -- - a boolean from the input tape
  -- - a symbol from the working tape
  -- A transition yields none if it causes the machine to halt.
  -- Otherwise it yields:
  -- - A new state
  -- - A symbol to be written to the working tape
  -- - Optionally a symbol to be written to the output tape
  -- - A value indicating whether the input tape head should move
  -- - A value indicating the direction in which the working tape head should move
  δ : Q -> Bool -> Γw → Option (Q × Γw × Option Γo × InputTapeDirection × WorkTapeDirection)
  -- Constraint: outputs never contain the default symbol
  no_default_output : ∀ q b w q' w' o itd wtd,
    δ q b w = some (q', w', o, itd, wtd) →
    ∀ γ, o = some γ → γ ≠ default

@[ext]
structure GenConfig (Γw Γo Q : Type u)
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
where
  (state : Q)
  (input : ℕ → Bool)
  (inputIndex : ℕ)
  (work : ℤ → Γw)
  (workIndex : ℤ)
  (output : List Γo)

def step {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) :
  Option (GenConfig Γw Γo Q) :=
match gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
  | none => none
  | some (q', w', out?, inDir, workDir) =>
    some {
      state := q',
      input := cfg.input,
      inputIndex := cfg.inputIndex + inDir,
      work := fun x => if (x = cfg.workIndex) then w' else cfg.work x,
      workIndex := cfg.workIndex + workDir,
      output :=
        match out? with
        | none => cfg.output
        | some g => cfg.output ++ [g]
    }

lemma step_preserves_no_default {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q) (cfg cfg' : GenConfig Γw Γo Q) :
  step gen cfg = some cfg' →
  default ∉ cfg.output →
  default ∉ cfg'.output := by
  intro h_step h_no_default
  unfold step at h_step
  split at h_step
  · contradiction
  · rename_i q' w' out? inDir workDir h_δ
    injection h_step with h_eq
    rw [← h_eq]
    simp only
    intro h
    cases out? with
    | none =>
      exact h_no_default h
    | some γ =>
      simp only [List.mem_append, List.mem_singleton] at h
      cases h with
      | inl h_old => exact h_no_default h_old
      | inr h_new =>
        have : γ ≠ default := gen.no_default_output _ _ _ _ _ _ _ _ h_δ γ rfl
        exact this h_new.symm

def initConfig {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) (input : ℕ → Bool) :
  GenConfig Γw Γo Q :=
{ state := gen.init
  input := input
  inputIndex := 0
  work := fun _ => gen.blank
  workIndex := 0
  output := []
}

def haltingConfig {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  (cfg : GenConfig Γw Γo Q) : Prop :=
step gen cfg = none

inductive Steps {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) :
  GenConfig Γw Γo Q →
  GenConfig Γw Γo Q →
  ℕ → Prop
| refl (cfg) :
    Steps gen cfg cfg 0
| step (cfg cfg' cfg'' n) :
    step gen cfg = some cfg' →
    Steps gen cfg' cfg'' n →
    Steps gen cfg cfg'' (n + 1)

namespace Steps

lemma trans {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  {gen : Generator Γw Γo Q} {cfg1 cfg2 cfg3 : GenConfig Γw Γo Q} {n m : ℕ} :
  Steps gen cfg1 cfg2 n → Steps gen cfg2 cfg3 m → Steps gen cfg1 cfg3 (n + m) := by
  intro h1 h2
  induction h1 with
  | refl =>
    rw [zero_add]
    exact h2
  | step cfg cfg' cfg'' n h_step h_steps ih =>
    have : n + 1 + m = n + m + 1 := by omega
    rw [this]
    apply Steps.step cfg cfg' cfg3 (n + m) h_step
    exact ih h2

end Steps

inductive Computes {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : GenConfig Γw Γo Q → List Γo → Prop
  | halt (cfg : GenConfig Γw Γo Q) :
      step gen cfg = none → Computes gen cfg cfg.output
  | step (cfg cfg' : GenConfig Γw Γo Q) (out : List Γo) :
      step gen cfg = some cfg' → Computes gen cfg' out → Computes gen cfg out

def StepsTo {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q)
(cfg : GenConfig Γw Γo Q)
(cfg' : GenConfig Γw Γo Q) : Prop :=
  ∃ n, Steps gen cfg cfg' n

namespace StepsTo

lemma refl {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg : GenConfig Γw Γo Q} :
  StepsTo gen cfg cfg :=
by
  unfold StepsTo
  refine ⟨0, ?_⟩
  exact Steps.refl cfg

lemma trans {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg1 cfg2 cfg3 : GenConfig Γw Γo Q} :
  StepsTo gen cfg1 cfg2 → StepsTo gen cfg2 cfg3 → StepsTo gen cfg1 cfg3 :=
by
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  exact ⟨n + m, Steps.trans h1 h2⟩

lemma computes {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  {gen : Generator Γw Γo Q} {cfg haltCfg : GenConfig Γw Γo Q} :
  StepsTo gen cfg haltCfg → step gen haltCfg = none →
  Computes gen cfg haltCfg.output := by
  intro ⟨n, h_steps⟩ h_halt
  induction h_steps with
  | refl cfg =>
    exact Computes.halt cfg h_halt
  | step cfg cfg' cfg'' n h_step h_steps' ih =>
    apply Computes.step cfg cfg' cfg''.output h_step
    exact ih h_halt

end StepsTo

namespace Computes

lemma no_default {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (out : List Γo) :
  Computes gen cfg out →
  default ∉ cfg.output →
  default ∉ out := by
  intro h_comp h_no_default
  induction h_comp with
  | halt cfg h_halt =>
    exact h_no_default
  | step cfg cfg' out h_step h_comp' ih =>
    apply ih
    exact step_preserves_no_default gen cfg cfg' h_step h_no_default

lemma of_StepsTo {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  {gen : Generator Γw Γo Q} {cfg cfg' : GenConfig Γw Γo Q} {out : List Γo} :
  Computes gen cfg out → StepsTo gen cfg cfg' → Computes gen cfg' out := by
  intro h_comp ⟨n, h_steps⟩
  induction h_steps generalizing out with
  | refl =>
    exact h_comp
  | step cfg cfg'' cfg' n h_step h_steps' ih =>
    cases h_comp with
    | halt cfg h_halt =>
      rw [h_halt] at h_step
      contradiction
    | step cfg cfg_next out' h_step' h_comp' =>
      have : cfg_next = cfg'' := by
        rw [h_step'] at h_step
        injection h_step
      rw [← this] at h_steps' ih
      exact ih h_comp'

end Computes

-- This captures the idea of a generator not being able to loop forever without
-- consuming an input bit.
-- This is not currently used, but it might be necessary to assume at some point.
def input_progressing {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : Prop :=
∀ cfg, ∃ cfg' n,
  Steps gen cfg cfg' n ∧ (haltingConfig gen cfg' ∨ cfg'.inputIndex > cfg.inputIndex)

end RandomisedGeneration
