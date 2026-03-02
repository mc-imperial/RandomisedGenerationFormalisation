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
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
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

def GeneratorSupports {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q) (S : Finset Q) : Prop :=
  gen.init ∈ S ∧
  ∀ q ∈ S, ∀ b w q' w' o itd wtd,
    gen.δ q b w = some (q', w', o, itd, wtd) → q' ∈ S

lemma generator_supports_univ {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [Fintype Q]
  (gen : Generator Γw Γo Q) :
  GeneratorSupports gen Finset.univ :=
  ⟨Finset.mem_univ _, fun _ _ _ _ _ _ _ _ _ _ => Finset.mem_univ _⟩

def Generator.restrictToSupport {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S) : Generator Γw Γo ↥S where
  init := ⟨gen.init, hS.1⟩
  blank := gen.blank
  δ := fun ⟨q, hq⟩ b w =>
    match h : gen.δ q b w with
    | none => none
    | some (q', w', o, itd, wtd) =>
        some (⟨q', hS.2 q hq b w q' w' o itd wtd h⟩, w', o, itd, wtd)

@[ext]
structure GenConfig (Γw Γo Q : Type u)
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
where
  (state : Q)
  (input : ℕ → Bool)
  (inputIndex : ℕ)
  (work : ℤ → Γw)
  (workIndex : ℤ)
  (output : List Γo)

def step {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
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

def initConfig {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
(gen : Generator Γw Γo Q) (input : ℕ → Bool) :
  GenConfig Γw Γo Q :=
{ state := gen.init
  input := input
  inputIndex := 0
  work := fun _ => gen.blank
  workIndex := 0
  output := []
}

def IsHalting {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : GenConfig Γw Γo Q) : Prop :=
step gen cfg = none

def stepN {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : Option (GenConfig Γw Γo Q))
  (n : ℕ) : Option (GenConfig Γw Γo Q) :=
  (fun c => c.bind (step gen))^[n] cfg

lemma stepN_zero {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : Option (GenConfig Γw Γo Q)) :
  stepN gen cfg 0 = cfg := rfl

lemma stepN_succ {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : Option (GenConfig Γw Γo Q)) (n : ℕ) :
  stepN gen cfg (n + 1) = (stepN gen cfg n).bind (step gen) := by
  simp only [stepN, Function.iterate_succ, Function.comp_apply]
  exact Function.iterate_succ_apply' (fun c => c.bind (step gen)) n cfg

lemma stepN_succ_front {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : Option (GenConfig Γw Γo Q)) (n : ℕ) :
  stepN gen cfg (n + 1) = stepN gen (cfg.bind (step gen)) n := by
  simp only [stepN, Function.iterate_succ_apply]

lemma stepN_none {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q) (n : ℕ) :
  stepN gen none n = none := by
  simp only [stepN]
  exact Function.iterate_fixed (by rfl) n

lemma stepN_halted {Γw Γo Q : Type u}
  [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg : GenConfig Γw Γo Q)
  (h : IsHalting gen cfg) (n : ℕ) :
  stepN gen (some cfg) (n + 1) = none := by
  simp only [IsHalting, stepN, Function.iterate_succ,
    Function.comp_apply, Option.bind_some] at *
  simp only [h]
  exact Function.iterate_fixed rfl n

lemma stepN_add {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} (a b : ℕ) (cfg : Option (GenConfig Γw Γo Q)) :
  stepN gen cfg (a + b) = stepN gen (stepN gen cfg a) b := by
  induction a generalizing cfg with
  | zero => simp [stepN]
  | succ a ih =>
    rw [Nat.succ_add, stepN_succ_front, stepN_succ_front]
    exact ih (cfg.bind (step gen))

lemma stepN_prefix {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg1 cfg2 : GenConfig Γw Γo Q} {m n : ℕ} :
  stepN gen (some cfg) m = some cfg1 →
  stepN gen (some cfg) n = some cfg2 →
  m ≤ n →
  stepN gen (some cfg1) (n - m) = some cfg2 := by
  intro h1 h2 hmn
  have key : stepN gen (some cfg) (m + (n - m)) = some cfg2 := by
    rwa [Nat.add_sub_cancel' hmn]
  rwa [stepN_add, h1] at key

lemma step_deterministic {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg1 cfg2 : GenConfig Γw Γo Q} :
  step gen cfg = some cfg1 →
  step gen cfg = some cfg2 →
  cfg1 = cfg2 := by
  intro h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

inductive Steps {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
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

lemma stepN_eq_Steps {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg cfg' : GenConfig Γw Γo Q) (n : ℕ) :
  stepN gen (some cfg) n = some cfg' ↔
  Steps gen cfg cfg' n := by
  induction n generalizing cfg cfg' with
  | zero =>
    simp only [stepN_zero, Option.some.injEq]
    constructor
    · intro h; cases h; exact Steps.refl _
    · intro h; cases h; rfl
  | succ n ih =>
      rw [stepN_succ_front]
      constructor
      · intro h
        cases h_step : step gen cfg with
        | none =>
          simp [h_step, stepN_none] at h
        | some cfg_next =>
          simp only [Option.bind_some, h_step] at h
          rw [ih] at h
          exact Steps.step cfg cfg_next cfg' n h_step h
      · intro h
        cases h with
        | step cfg cfg_next cfg' n h_step h_steps =>
          simp only [Option.bind_some, h_step]
          rw [ih]
          exact h_steps

lemma stepN_none_iff_halted {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (cfg cfg' : GenConfig Γw Γo Q) (n : ℕ) :
  stepN gen (some cfg) n = some cfg' ∧ IsHalting gen cfg' ↔
  Steps gen cfg cfg' n ∧ IsHalting gen cfg' := by
  simp [stepN_eq_Steps]

lemma step_preserves_input {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg' : GenConfig Γw Γo Q} :
  RandomisedGeneration.step gen cfg = some cfg' →
  cfg'.input = cfg.input := by
  simp only [step]
  split
  · simp
  · intro h
    simp only [Option.some.injEq] at h
    rw [← h]

namespace Steps

lemma trans {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
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

lemma unique {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg1 cfg2 : GenConfig Γw Γo Q} {n : ℕ} :
  Steps gen cfg cfg1 n →
  Steps gen cfg cfg2 n →
  cfg1 = cfg2 := by
  intro h1 h2
  induction h1 with
  | refl => cases h2; rfl
  | step cfg cfg' cfg1 n h_step h_steps ih =>
    cases h2 with
    | step _ cfg'' _ _ h_step' h_steps' =>
      have h_eq : cfg' = cfg'' := step_deterministic h_step h_step'
      subst h_eq
      exact ih h_steps'

lemma prefix_extends {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg1 cfg2 : GenConfig Γw Γo Q} {m n : ℕ} :
  Steps gen cfg cfg1 m →
  Steps gen cfg cfg2 n →
  m ≤ n →
  Steps gen cfg1 cfg2 (n - m) := by
  intro h1 h2 hmn
  rw [← stepN_eq_Steps] at h1 h2 ⊢
  exact stepN_prefix h1 h2 hmn

lemma step_inputIndex_mono {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg' : GenConfig Γw Γo Q} :
  RandomisedGeneration.step gen cfg = some cfg' →
  cfg.inputIndex ≤ cfg'.inputIndex := by
  simp only [RandomisedGeneration.step]
  intro h
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only
    omega

lemma inputIndex_mono {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg cfg' : GenConfig Γw Γo Q} {n : ℕ} :
  Steps gen cfg cfg' n →
  cfg.inputIndex ≤ cfg'.inputIndex := by
  intro h
  induction h with
  | refl =>
    exact le_refl _
  | step cfg cfg' cfg'' n h_step _ ih =>
    exact le_trans (step_inputIndex_mono h_step) ih

end Steps

inductive Computes {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
(gen : Generator Γw Γo Q) : GenConfig Γw Γo Q → List Γo → Prop
  | halt (cfg : GenConfig Γw Γo Q) :
      step gen cfg = none → Computes gen cfg cfg.output
  | step (cfg cfg' : GenConfig Γw Γo Q) (out : List Γo) :
      step gen cfg = some cfg' → Computes gen cfg' out → Computes gen cfg out

def Reachable {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
(gen : Generator Γw Γo Q)
(cfg : GenConfig Γw Γo Q)
(cfg' : GenConfig Γw Γo Q) : Prop :=
  ∃ n, Steps gen cfg cfg' n

namespace Reachable

lemma refl {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  {cfg : GenConfig Γw Γo Q} :
  Reachable gen cfg cfg :=
by
  unfold Reachable
  refine ⟨0, ?_⟩
  exact Steps.refl cfg

lemma trans {Γw Γo Q}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  {cfg1 cfg2 cfg3 : GenConfig Γw Γo Q} :
  Reachable gen cfg1 cfg2 → Reachable gen cfg2 cfg3 → Reachable gen cfg1 cfg3 :=
by
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  exact ⟨n + m, Steps.trans h1 h2⟩

lemma computes {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  {gen : Generator Γw Γo Q} {cfg haltCfg : GenConfig Γw Γo Q} :
  Reachable gen cfg haltCfg → step gen haltCfg = none →
  Computes gen cfg haltCfg.output := by
  intro ⟨n, h_steps⟩ h_halt
  induction h_steps with
  | refl cfg =>
    exact Computes.halt cfg h_halt
  | step cfg cfg' cfg'' n h_step h_steps' ih =>
    apply Computes.step cfg cfg' cfg''.output h_step
    exact ih h_halt

end Reachable

lemma reachable_input_eq {Γw Γo Q : Type u}
[FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {f : ℕ → Bool} {cfg : GenConfig Γw Γo Q} :
  Reachable gen (initConfig gen f) cfg →
  cfg.input = f := by
  rintro ⟨n, h_steps⟩
  have : ∀ (n : ℕ) (start cfg : GenConfig Γw Γo Q),
      start.input = f →
      Steps gen start cfg n →
      cfg.input = f := by
    intro n
    induction n with
    | zero =>
      intro start cfg h_input h_steps
      cases h_steps
      exact h_input
    | succ n ih =>
      intro start cfg h_input h_steps
      cases h_steps with
      | step start mid cfg n h_step h_steps' =>
        apply ih mid cfg _ h_steps'
        rw [step_preserves_input h_step]
        exact h_input
  exact this n (initConfig gen f) cfg (by simp [initConfig]) h_steps

private lemma sum_if_two_pow_lt (f : ℕ → Bool) : ∀ k,
    (∑ j ∈ Finset.range k, if f j then 2^j else 0) < 2^k
  | 0 => by simp
  | k+1 => by
      rw [Finset.sum_range_succ]
      have ih := sum_if_two_pow_lt f k
      split_ifs with hfk
      · linarith [pow_succ 2 k]
      · omega

lemma testBit_sum_pow (f : ℕ → Bool) (k i : ℕ) (hi : i < k) :
    (∑ j ∈ Finset.range k, if f j then 2^j else 0).testBit i = f i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hik : i < k
    · -- the 2^k term doesn't affect bit i since i < k
      have h_low := sum_if_two_pow_lt f k
      cases hfk : f k with
      | false => simp [ih hik]
      | true =>
        simp only [ite_true]
        rw [add_comm]
        rw [Nat.testBit_two_pow_add_gt hik]
        exact ih hik
    · -- i = k
      have hik' : i = k := by omega
      subst hik'
      have h_low := sum_if_two_pow_lt f i
      cases hfi : f i with
      | false =>
        exact Nat.testBit_lt_two_pow h_low
      | true =>
        simp only [ite_true]
        rw [add_comm]
        simp only [Nat.testBit_two_pow_add_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
        exact Nat.testBit_lt_two_pow h_low

namespace Computes

lemma of_Reachable {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
  {gen : Generator Γw Γo Q} {cfg cfg' : GenConfig Γw Γo Q} {out : List Γo} :
  Computes gen cfg out → Reachable gen cfg cfg' → Computes gen cfg' out := by
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

lemma to_stepN {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {cfg : GenConfig Γw Γo Q} {w : List Γo} :
  Computes gen cfg w →
  ∃ k haltCfg,
    stepN gen (some cfg) k = some haltCfg ∧
    RandomisedGeneration.step gen haltCfg = none ∧
    haltCfg.output = w := by
  intro h
  induction h with
  | halt cfg h_halt =>
    exact ⟨0, cfg, by simp [stepN], h_halt, rfl⟩
  | step cfg cfg' w h_step _ ih =>
    obtain ⟨k, haltCfg, h_stepN, h_halt, h_out⟩ := ih
    refine ⟨k + 1, haltCfg, ?_, h_halt, h_out⟩
    rw [stepN_succ_front]
    simp [h_step, h_stepN]

lemma congr_input {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {f g : ℕ → Bool} {w : List Γo} {k : ℕ} :
  Computes gen (initConfig gen f) w →
  (∀ i < k, f i = g i) →
  (∀ cfg, Reachable gen (initConfig gen f) cfg →
    cfg.inputIndex < k) →
  Computes gen (initConfig gen g) w := by
  intro h_comp h_agree h_bound
  obtain ⟨n, haltCfg, h_stepN, h_halt, h_out⟩ := h_comp.to_stepN
  suffices ∀ (n : ℕ) (cfg : GenConfig Γw Γo Q),
    Reachable gen (initConfig gen f) cfg →
    stepN gen (some cfg) n = some haltCfg →
    Computes gen { cfg with input := g } w by
    have := this n (initConfig gen f) (Reachable.refl gen) h_stepN
    convert this using 1
  intro n
  induction n with
  | zero =>
    intro cfg h_reach h_stepN'
    simp only [stepN_zero, Option.some.injEq] at h_stepN'
    subst h_stepN'
    rw [h_out]
    apply Computes.halt
    simp only [RandomisedGeneration.step]
    rw [← h_agree cfg.inputIndex (h_bound cfg h_reach)]
    simp only [RandomisedGeneration.step] at h_halt
    rw [reachable_input_eq h_reach] at h_halt
    split
    · rfl
    · rename_i q' w' out? inDir workDir heq
      simp [heq] at h_halt
  | succ n ih =>
    intro cfg h_reach h_stepN'
    rw [stepN_succ_front] at h_stepN'
    cases h_step : RandomisedGeneration.step gen cfg with
    | none =>
      simp [h_step, stepN_none] at h_stepN'
    | some cfg_next =>
      simp only [h_step, Option.bind_some] at h_stepN'
      have h_bit : f cfg.inputIndex = g cfg.inputIndex :=
        h_agree cfg.inputIndex (h_bound cfg h_reach)
      have h_step_g : RandomisedGeneration.step gen { cfg with input := g } =
          some { cfg_next with input := g } := by
        simp only [RandomisedGeneration.step] at h_step ⊢
        rw [reachable_input_eq h_reach] at h_step
        rw [← h_bit]
        split
        · rename_i heq
          simp [heq] at h_step
        · rename_i q' w' out? inDir workDir heq
          simp only [heq] at h_step
          simp only [Option.some.injEq] at h_step
          simp only [Option.some.injEq]
          ext <;> simp [← h_step]
      have h_reach' : Reachable gen (initConfig gen f) cfg_next :=
        Reachable.trans gen h_reach
          ⟨1, Steps.step _ _ _ _ h_step (Steps.refl _)⟩
      apply Computes.step _ _ _ h_step_g
      exact ih cfg_next h_reach' h_stepN'

lemma finite_input_reads {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {f : ℕ → Bool} {w : List Γo} :
  Computes gen (initConfig gen f) w →
  ∃ k, ∀ cfg : GenConfig Γw Γo Q,
    Reachable gen (initConfig gen f) cfg →
    cfg.inputIndex < k := by
  intro h_comp
  obtain ⟨n, haltCfg, h_stepN, h_halt, h_out⟩ := h_comp.to_stepN
  refine ⟨haltCfg.inputIndex + 1, ?_⟩
  intro cfg ⟨m, h_steps⟩
  have h_steps_to_halt : Steps gen (initConfig gen f) haltCfg n := by
    rwa [stepN_eq_Steps] at h_stepN
  by_cases hm : m ≤ n
  · -- cfg is on the path to haltCfg
    have h_cfg_to_halt := Steps.prefix_extends h_steps h_steps_to_halt hm
    have h_mono := Steps.inputIndex_mono h_cfg_to_halt
    omega
  · -- cfg is past haltCfg, impossible
    push_neg at hm
    have h_halt_to_cfg := Steps.prefix_extends h_steps_to_halt h_steps (by omega)
    have := stepN_halted gen haltCfg h_halt (m - n - 1)
    rw [← stepN_eq_Steps] at h_halt_to_cfg
    cases h_mn : m - n with
    | zero => omega
    | succ k =>
      rw [h_mn] at h_halt_to_cfg
      rw [stepN_halted gen haltCfg h_halt k] at h_halt_to_cfg
      simp at h_halt_to_cfg

lemma exists_natTestBit {Γw Γo Q : Type u}
[FinEnum Γw]
[Inhabited Γo] [FinEnum Γo]
{gen : Generator Γw Γo Q} {f : ℕ → Bool} {w : List Γo} :
  Computes gen (initConfig gen f) w →
  ∃ m : ℕ, Computes gen (initConfig gen (Nat.testBit m)) w := by
  intro h_comp
  obtain ⟨k, h_bound⟩ := h_comp.finite_input_reads
  let m := ∑ i ∈ Finset.range k, if f i then 2^i else 0
  refine ⟨m, congr_input h_comp (k := k) ?_ ?_⟩
  · intro i hi
    exact (testBit_sum_pow f k i hi).symm
  · exact h_bound

end Computes

def GenConfig.mapState {Γw Γo Q Q' : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (f : Q → Q') (cfg : GenConfig Γw Γo Q) : GenConfig Γw Γo Q' :=
  { cfg with state := f cfg.state }

@[simp]
lemma GenConfig.mapState_state {Γw Γo Q Q' : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (f : Q → Q') (cfg : GenConfig Γw Γo Q) :
    (cfg.mapState f).state = f cfg.state := rfl

@[simp]
lemma GenConfig.mapState_input {Γw Γo Q Q' : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (f : Q → Q') (cfg : GenConfig Γw Γo Q) :
    (cfg.mapState f).input = cfg.input := rfl

@[simp]
lemma GenConfig.mapState_output {Γw Γo Q Q' : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (f : Q → Q') (cfg : GenConfig Γw Γo Q) :
    (cfg.mapState f).output = cfg.output := rfl

@[simp]
lemma GenConfig.mapState_id {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (cfg : GenConfig Γw Γo Q) :
    cfg.mapState id = cfg := by
  simp [GenConfig.mapState]

lemma initConfig_mapState {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S)
    (input : ℕ → Bool) :
    (initConfig (gen.restrictToSupport S hS) input).mapState Subtype.val =
    initConfig gen input := by
  simp [initConfig, GenConfig.mapState, Generator.restrictToSupport]

-- lemma step_restrictToSupport {Γw Γo Q : Type u}
--     [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
--     (gen : Generator Γw Γo Q)
--     (S : Finset Q) (hS : GeneratorSupports gen S)
--     (cfg : GenConfig Γw Γo ↥S) :
--     (step (gen.restrictToSupport S hS) cfg).map (·.mapState Subtype.val) =
--     step gen (cfg.mapState Subtype.val) := by
--   simp [step, Generator.restrictToSupport, GenConfig.mapState, Option.map]
--   sorry

lemma step_restrictToSupport {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S)
    (cfg : GenConfig Γw Γo ↥S) :
    (step (gen.restrictToSupport S hS) cfg).map (·.mapState Subtype.val) =
    step gen (cfg.mapState Subtype.val) := by
  -- We match on the transition of the original generator
  unfold step Generator.restrictToSupport
  cases h : gen.δ ↑cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex)
  · -- Both sides reduce to 'none'
    simp only [Int.reduceNeg, GenConfig.mapState_state, GenConfig.mapState_input,
      GenConfig.mapState_output]
    simp only [GenConfig.mapState, Int.reduceNeg, h, Option.map_eq_none_iff]
    split <;> simp only [Int.reduceNeg, reduceCtorEq]
    rename_i h_match
    rename_i h_match
    split at h_match
    · contradiction -- This handles the case where the match thought it was 'none'
    · rename_i h_some
      cases h.symm.trans h_some
  · -- Both sides reduce to 'some' with the same data
    rename_i res
    obtain ⟨q', w', out?, inDir, workDir⟩ := res
    simp only [GenConfig.mapState, Int.reduceNeg, h, Option.map_eq_some_iff, GenConfig.mk.injEq]
    split
    · rename_i h_match
      exfalso
      sorry
    · sorry

lemma step_restrictToSupport_backward {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S)
    (cfg : GenConfig Γw Γo ↥S)
    (cfg' : GenConfig Γw Γo Q)
    (h : step gen (cfg.mapState Subtype.val) = some cfg') :
    ∃ cfg'' : GenConfig Γw Γo ↥S,
      step (gen.restrictToSupport S hS) cfg = some cfg'' ∧
      cfg''.mapState Subtype.val = cfg' := by
  have key := step_restrictToSupport gen S hS cfg
  rw [h] at key
  sorry

lemma restrictToSupport_Computes_forward {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S)
    {input : ℕ → Bool} {w : List Γo} :
    Computes (gen.restrictToSupport S hS)
      (initConfig (gen.restrictToSupport S hS) input) w →
    Computes gen (initConfig gen input) w := by
  intro h
  -- Generalise to arbitrary cfg, not just initConfig
  suffices ∀ (cfg : GenConfig Γw Γo ↥S) (w : List Γo),
      Computes (gen.restrictToSupport S hS) cfg w →
      Computes gen (cfg.mapState Subtype.val) w by
    have := this _ _ h
    rwa [initConfig_mapState] at this
  intro cfg w hc
  induction hc with
  | halt cfg h_halt =>
    apply Computes.halt
    have key := step_restrictToSupport gen S hS cfg
    simp [h_halt] at key
    simpa using key.symm
  | step cfg cfg' w h_step _ ih =>
    apply Computes.step _ _ _ _ ih
    have key := step_restrictToSupport gen S hS cfg
    simp [h_step] at key
    sorry

lemma restrictToSupport_Computes_backward {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S : Finset Q) (hS : GeneratorSupports gen S)
    {input : ℕ → Bool} {w : List Γo} :
    Computes gen (initConfig gen input) w →
    Computes (gen.restrictToSupport S hS)
      (initConfig (gen.restrictToSupport S hS) input) w := by
  intro h
  -- Generalise: any cfg reachable from initConfig has state in S
  suffices ∀ (cfg : GenConfig Γw Γo Q) (w : List Γo),
      Computes gen cfg w →
      ∀ (cfgS : GenConfig Γw Γo ↥S),
        cfgS.mapState Subtype.val = cfg →
        Computes (gen.restrictToSupport S hS) cfgS w by
    have := this _ _ h (initConfig (gen.restrictToSupport S hS) input)
      (initConfig_mapState gen S hS input)
    exact this
  intro cfg w hc
  induction hc with
  | halt cfg h_halt =>
    intro cfgS h_eq
    sorry
  | step cfg cfg' w h_step _ ih =>
    intro cfgS h_eq
    obtain ⟨cfgS', h_stepS, h_eq'⟩ :=
      step_restrictToSupport_backward gen S hS cfgS cfg'
        (by rw [h_eq]; exact h_step)
    apply Computes.step _ _ _ h_stepS
    exact ih cfgS' h_eq'

end RandomisedGeneration
