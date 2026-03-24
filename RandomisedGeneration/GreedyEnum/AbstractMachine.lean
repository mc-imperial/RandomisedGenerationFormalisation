/-
══════════════════════════════════════════════════════════════════════════════
  Counter-based abstract machine for greedy enumeration.

  Replaces the (len, idx)-based abstract machine with one that mirrors
  the TM2's binary counter directly. Each round: run the generator for
  counter.length steps on counterToInput counter, check output, increment.

  This file provides:
    • counterEnumStep, CounterEnumRecognises — the abstract machine
    • greedy generator helper lemmas (non-private)
    • counterIterN and its arithmetic properties
    • CounterEnumRecognises_iff_Computes — the main equivalence
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib
import RandomisedGeneration.Generator
import RandomisedGeneration.GreedyEnum.CounterManipulation

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

/-- One round of the counter-based enumeration.
    Run the greedy generator on `counterToInput counter` for `counter.length`
    steps. If the generator halts within those steps and the output matches
    `target`, return `none` (match found). Otherwise return
    `some (counterIncrement counter)`. -/
def counterEnumStep
    (gen : Generator Γw Γo Q) (target : List Γo)
    (counter : List (ULift.{u} Bool)) : Option (List (ULift.{u} Bool)) :=
  let input := counterToInput counter
  let cfg := stepNHalt gen (initConfig gen input) counter.length
  match step gen cfg with
  | some _ => some (counterIncrement counter)  -- not halted (ran out of steps)
  | none =>                                     -- halted
    if cfg.output = target then none            -- match!
    else some (counterIncrement counter)        -- output mismatch

/-- The counter-based enumeration recognises `w` if iterating counterEnumStep
    starting from `[]` eventually returns `none`. -/
def CounterEnumRecognises (gen : Generator Γw Γo Q) (w : List Γo) : Prop :=
  ∃ n, (fun c => c.bind (counterEnumStep gen w))^[n]
    (some ([] : List (ULift.{u} Bool))) = none

lemma counterEnumStep_eq_none_iff (gen : Generator Γw Γo Q) (target : List Γo)
    (counter : List (ULift.{u} Bool)) :
    counterEnumStep gen target counter = none ↔
    (IsHalting gen (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length) ∧
     (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length).output = target) := by
  unfold counterEnumStep IsHalting
  simp only
  cases h : step gen (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length) with
  | none =>
    simp
  | some _ =>
    simp

lemma counterEnumStep_ne_none (gen : Generator Γw Γo Q) (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (h : counterEnumStep gen target counter ≠ none) :
    counterEnumStep gen target counter = some (counterIncrement counter) := by
  unfold counterEnumStep at h ⊢
  simp only
  cases hstep : step gen (stepNHalt gen (initConfig gen (counterToInput counter)) counter.length)
    with
  | some _ => rfl
  | none =>
    simp only [hstep, ne_eq, ite_eq_left_iff, reduceCtorEq, imp_false, Decidable.not_not,
      ite_eq_right_iff] at h ⊢
    exact h

/-- For a greedy generator, the inputIndex after n steps equals
    the starting inputIndex plus n. -/
lemma greedy_inputIndex_eq_steps
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy)
    (cfg cfg' : GenConfig Γw Γo Q) (n : ℕ)
    (h : Steps gen cfg cfg' n) :
    cfg'.inputIndex = cfg.inputIndex + n := by
  induction h with
  | refl => omega
  | step cfg cfg'' cfg' n hStep _ ih =>
    rw [ih]
    unfold step at hStep
    cases hδ : gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
    | none => simp [hδ] at hStep
    | some val =>
      obtain ⟨q', w', o, itd, wd⟩ := val
      simp only [hδ, Int.reduceNeg, Option.some.injEq] at hStep
      have := hGreedy _ _ _ _ _ _ _ _ hδ
      subst this; rw [← hStep]; simp; omega

/-- If two input functions agree on bits < n, and the greedy generator takes
    j ≤ n steps on input f, then it also takes j steps on input g with the
    same configuration (modulo input function). -/
lemma greedy_stepN_agree'
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy)
    (f g : ℕ → Bool) (n : ℕ)
    (hAgree : ∀ i, i < n → f i = g i)
    (j : ℕ) (hj : j ≤ n)
    (cfgF : GenConfig Γw Γo Q)
    (hStepN : stepN gen (some (initConfig gen f)) j = some cfgF) :
    stepN gen (some (initConfig gen g)) j = some { cfgF with input := g } := by
  induction j generalizing cfgF with
  | zero =>
    simp only [stepN, Function.iterate_zero, id_eq, Option.some.injEq] at hStepN ⊢
    subst hStepN; simp [initConfig]
  | succ j ih =>
    rw [stepN_succ] at hStepN ⊢
    cases hprev : stepN gen (some (initConfig gen f)) j with
    | none => simp [hprev] at hStepN
    | some cfgF_prev =>
      simp only [hprev, Option.bind_some] at hStepN
      rw [ih (by omega) cfgF_prev hprev]
      simp only [Option.bind_some]
      have hIdxJ : cfgF_prev.inputIndex = j := by
        have := greedy_inputIndex_eq_steps gen hGreedy _ _ j
          ((stepN_eq_Steps gen _ _ j).mp hprev)
        simp only [initConfig, zero_add] at this; exact this
      have hInput : cfgF_prev.input = f :=
        reachable_input_eq ⟨j, (stepN_eq_Steps gen _ _ j).mp hprev⟩
      unfold step at hStepN ⊢; simp only at hStepN ⊢
      rw [hIdxJ, hInput] at hStepN; rw [hIdxJ]
      rw [hAgree j (by omega)] at hStepN
      split at hStepN
      · simp at hStepN
      · rename_i q' w' o itd wd hδ
        have hitd := hGreedy _ _ _ _ _ _ _ _ hδ; subst hitd
        simp only [Option.some.injEq] at hStepN ⊢; rw [← hStepN]

/-- If a greedy generator computes `w` on `f` reading `< k` bits, and `g`
    agrees with `f` on bits `< k` and `len ≥ k`, then the generator halts
    within `len` steps on input `g` with output `w`. -/
lemma greedy_computes_within
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy)
    (f g : ℕ → Bool) (len : ℕ) (w : List Γo)
    (hComp : Computes gen (initConfig gen f) w)
    (k : ℕ)
    (hBound : ∀ cfg, Reachable gen (initConfig gen f) cfg → cfg.inputIndex < k)
    (hLen : len ≥ k)
    (hAgree : ∀ i, i < k → g i = f i) :
    ∃ steps, steps ≤ len ∧
      IsHalting gen (stepNHalt gen (initConfig gen g) steps) ∧
      (stepNHalt gen (initConfig gen g) steps).output = w := by
  obtain ⟨n, haltCfg, hStepN, hHalt, hOut⟩ := hComp.to_stepN
  have hSteps := (stepN_eq_Steps gen _ _ n).mp hStepN
  have hIdx_n := greedy_inputIndex_eq_steps gen hGreedy _ _ n hSteps
  simp only [initConfig, zero_add] at hIdx_n
  have hn_lt_k : n < k := by rw [← hIdx_n]; exact hBound _ ⟨n, hSteps⟩
  have hStepN' := greedy_stepN_agree' gen hGreedy f g n
    (fun i hi => (hAgree i (by omega)).symm) n le_rfl haltCfg hStepN
  have hHalt' : IsHalting gen { haltCfg with input := g } := by
    simp only [IsHalting, step] at hHalt ⊢
    rw [reachable_input_eq ⟨n, hSteps⟩, hIdx_n] at hHalt
    rw [hIdx_n, show g n = f n from hAgree n hn_lt_k]
    cases hδ : gen.δ haltCfg.state (f n) (haltCfg.work haltCfg.workIndex) with
    | none => simp [hδ] at hHalt ⊢
    | some val => simp [hδ] at hHalt
  exact ⟨n, by omega,
    by rw [stepNHalt_eq_of_stepN gen _ _ n hStepN']; exact hHalt',
    by rw [stepNHalt_eq_of_stepN gen _ _ n hStepN']; exact hOut⟩

lemma counterEnum_iterates (gen : Generator Γw Γo Q) (w : List Γo) (n : ℕ)
    (hNoMatch : ∀ m, m < n →
      counterEnumStep gen w (counterIterN m) ≠ none) :
    (fun c => c.bind (counterEnumStep gen w))^[n]
      (some ([] : List (ULift.{u} Bool))) = some (counterIterN n) := by
  induction n with
  | zero => simp [counterIterN]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih (fun m hm => hNoMatch m (by omega))]
    simp only [Option.bind_some]
    have hne := hNoMatch n (by omega)
    rw [counterEnumStep_ne_none gen w _ hne]
    simp [counterIterN]

-- ═══════════════════════════════════════════════════════════════════════════
-- Section 7: Main equivalence
-- ═══════════════════════════════════════════════════════════════════════════

/-- If counterEnumStep returns none at some counterIterN n, the iteration
    reaches none (possibly earlier). -/
private lemma iteration_reaches_none
    (gen : Generator Γw Γo Q) (w : List Γo) (n : ℕ)
    (hMatch : counterEnumStep gen w (counterIterN n) = none) :
    CounterEnumRecognises gen w := by
  have hEx : ∃ m, counterEnumStep gen w (counterIterN m) = none := ⟨n, hMatch⟩
  let m₀ := Nat.find hEx
  have hm₀_match := Nat.find_spec hEx
  have hm₀_first : ∀ j, j < m₀ →
      counterEnumStep gen w (counterIterN j) ≠ none :=
    fun j hj => Nat.find_min hEx hj
  exact ⟨m₀ + 1, by
    rw [Function.iterate_succ_apply', counterEnum_iterates gen w m₀ hm₀_first]
    simp only [Option.bind_some]
    exact hm₀_match
    ⟩

theorem CounterEnumRecognises_iff_Computes
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy) (w : List Γo) :
    CounterEnumRecognises gen w ↔
    ∃ input : ℕ → Bool, Computes gen (initConfig gen input) w := by
  constructor
  · -- Forward: CounterEnumRecognises → ∃ input, Computes
    -- By induction on iteration count, find the counter where a match occurred,
    -- then extract the witness from stepNHalt_Computes.
    intro ⟨n, hn⟩
    suffices ∀ n (counter : List (ULift.{u} Bool)),
        (fun c => c.bind (counterEnumStep gen w))^[n] (some counter) = none →
        ∃ input, Computes gen (initConfig gen input) w by
      exact this n [] hn
    intro n
    induction n with
    | zero => intro c h; simp at h
    | succ n ih =>
      intro counter hn'
      rw [Function.iterate_succ_apply'] at hn'
      cases hiter : (fun c => c.bind (counterEnumStep gen w))^[n] (some counter) with
      | none =>
        -- The iteration already reached none at step n
        exact ih counter (by simpa using hiter)
      | some counter' =>
        -- The iteration produced some counter', then one more step gave none
        rw [hiter] at hn'
        simp only [Option.bind_some] at hn'
        -- hn' : counterEnumStep gen w counter' = none
        have ⟨hHalt, hOut⟩ := (counterEnumStep_eq_none_iff gen w counter').mp hn'
        exact ⟨counterToInput counter', hOut ▸ stepNHalt_Computes gen _ _ hHalt⟩
  · -- Backward: ∃ input, Computes → CounterEnumRecognises
    -- Strategy: reduce to Nat.testBit m, then pick n = m + 2^k to ensure
    -- counterIterN n is long enough and its input agrees with Nat.testBit m
    -- on the relevant positions.
    intro ⟨f, hComp⟩
    -- Step 1: reduce to Nat.testBit m
    obtain ⟨m, hCompM⟩ := Computes.exists_natTestBit hComp
    obtain ⟨k, hBound⟩ := Computes.finite_input_reads hCompM
    -- Step 2: exists_natTestBit gives m < 2^k (from the proof of finite_input_reads)
    -- We reconstruct this: m = ∑ i < k, if f i then 2^i else 0, so m < 2^k.
    -- Actually, exists_natTestBit gives us an arbitrary m. We need m < 2^k.
    -- The proof of exists_natTestBit constructs m = ∑ i < k', ... for some k'.
    -- We can get a uniform bound by re-doing the argument:
    -- Computes.finite_input_reads on hCompM gives k' such that all reachable
    -- configs have inputIndex < k'. Then Nat.testBit m i = false for i ≥ k'
    -- would give m < 2^k', but we don't know this about m.
    -- SIMPLER: just use n = m + 2^k directly, without needing m < 2^k.
    -- testBit_add_two_pow needs m < 2^k, but Nat.testBit_two_pow_add_gt
    -- (which is `testBit (2^k + m) i = testBit m i` for `i < k`)
    -- does NOT need m < 2^k!
    let n := m + 2 ^ k
    -- counterToInput (counterIterN n) agrees with Nat.testBit m on bits < k
    have hInputAgree : ∀ i, i < k →
        counterToInput (counterIterN n) i = Nat.testBit m i := by
      intro i hi
      rw [counterToInput_counterIterN]
      change Nat.testBit (m + 2 ^ k) i = Nat.testBit m i
      rw [add_comm]
      exact Nat.testBit_two_pow_add_gt hi m
    -- counterIterN n is long enough
    have hLenN : (counterIterN n).length ≥ k := by
      have := counterIterN_length_ge n k (by omega : n ≥ 2 ^ k); omega
    -- Step 3: generator halts on counterToInput (counterIterN n) within length steps
    obtain ⟨steps, hStepsLe, hHalt, hOut⟩ := greedy_computes_within gen hGreedy
      (Nat.testBit m)
      (counterToInput (counterIterN n))
      (counterIterN n).length w hCompM k hBound hLenN hInputAgree
    -- stepNHalt at counter.length halts with correct output
    have hHaltLen : IsHalting gen
        (stepNHalt gen (initConfig gen (counterToInput (counterIterN n)))
          (counterIterN n).length) :=
      stepNHalt_fixed gen _ steps hHalt _ hStepsLe ▸ hHalt
    have hOutLen : (stepNHalt gen (initConfig gen (counterToInput (counterIterN n)))
        (counterIterN n).length).output = w :=
      stepNHalt_fixed gen _ steps hHalt _ hStepsLe ▸ hOut
    -- Step 4: counterEnumStep at counterIterN n returns none
    have hMatch : counterEnumStep gen w (counterIterN n) = none := by
      rw [counterEnumStep_eq_none_iff]; exact ⟨hHaltLen, hOutLen⟩
    -- Step 5: the iteration reaches none
    exact iteration_reaches_none gen w n hMatch

end GreedyEnum

end RandomisedGeneration
