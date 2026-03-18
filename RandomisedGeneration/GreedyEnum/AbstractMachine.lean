import Mathlib
import RandomisedGeneration.Generator

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

/-- The state of the greedy enumeration machine. -/
structure GreedyEnumState (Γw Γo Q : Type u)
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] where
  currentLen : ℕ      -- length of current bit string
  currentIdx : ℕ      -- index within strings of this length
  stepsRemaining : ℕ  -- steps left for current instance
  inst : GenConfig Γw Γo Q  -- current generator config

/-- Convert (len, idx) to an input function: idx's bits padded/truncated to len,
    then false beyond. -/
def bitStringInput (len idx : ℕ) : ℕ → Bool :=
  fun i => if i < len then Nat.testBit idx i else false

/-- Advance to the next bit string in the enumeration. -/
def nextEnumState (gen : Generator Γw Γo Q) (len idx : ℕ) :
    GreedyEnumState Γw Γo Q :=
  if idx + 1 < 2 ^ len then
    { currentLen := len, currentIdx := idx + 1,
      stepsRemaining := len,
      inst := initConfig gen (bitStringInput len (idx + 1)) }
  else
    { currentLen := len + 1, currentIdx := 0,
      stepsRemaining := len + 1,
      inst := initConfig gen (bitStringInput (len + 1) 0) }

/-- One step of the greedy enumeration. Returns none if a match is found. -/
def greedyEnumStep (gen : Generator Γw Γo Q) (target : List Γo)
    (ges : GreedyEnumState Γw Γo Q) :
    Option (GreedyEnumState Γw Γo Q) :=
  match step gen ges.inst with
  | none =>
    -- Generator halted: check output
    if ges.inst.output = target then none
    else some (nextEnumState gen ges.currentLen ges.currentIdx)
  | some cfg' =>
    if ges.stepsRemaining = 0 then
      -- Out of bits: move to next string
      some (nextEnumState gen ges.currentLen ges.currentIdx)
    else
      some { ges with inst := cfg', stepsRemaining := ges.stepsRemaining - 1 }

/-- Initial state: start with the length-0 string (empty). -/
def initGreedyEnumState (gen : Generator Γw Γo Q) :
    GreedyEnumState Γw Γo Q :=
  { currentLen := 0, currentIdx := 0, stepsRemaining := 0,
    inst := initConfig gen (bitStringInput 0 0) }

/-- The greedy enumeration recognises w if iterating greedyEnumStep
    eventually returns none. -/
def GreedyEnumRecognises (gen : Generator Γw Γo Q) (w : List Γo) : Prop :=
  ∃ n, (fun s => s.bind (greedyEnumStep gen w))^[n] (some (initGreedyEnumState gen)) = none

private lemma greedy_inputIndex_eq_steps
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (cfg cfg' : GenConfig Γw Γo Q) (n : ℕ)
    (h : Steps gen cfg cfg' n) :
    cfg'.inputIndex = cfg.inputIndex + n := by
  induction h with
  | refl => omega
  | step cfg cfg'' cfg' n hStep _ ih =>
    rw [ih]; clear ih
    unfold step at hStep
    cases hδ : gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
    | none => simp [hδ] at hStep
    | some val =>
      obtain ⟨q', w', o, itd, wd⟩ := val
      simp only [hδ, Int.reduceNeg, Option.some.injEq] at hStep
      have := hGreedy _ _ _ _ _ _ _ _ hδ
      subst this; rw [← hStep]; simp; omega

private lemma greedy_inputIndex_at_step
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (f : ℕ → Bool) (j : ℕ) (cfg : GenConfig Γw Γo Q)
    (h : stepN gen (some (initConfig gen f)) j = some cfg) :
    cfg.inputIndex = j := by
  have := greedy_inputIndex_eq_steps gen hGreedy _ _ j ((stepN_eq_Steps gen _ _ j).mp h)
  simp only [initConfig, zero_add] at this
  exact this

private lemma greedy_stepN_agree
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (f g : ℕ → Bool) (n : ℕ)
    (hAgree : ∀ i, i < n → f i = g i) :
    ∀ j, j ≤ n →
      ∀ cfgF, stepN gen (some (initConfig gen f)) j = some cfgF →
        stepN gen (some (initConfig gen g)) j = some { cfgF with input := g } := by
  intro j hj
  induction j with
  | zero =>
    intro cfg h
    simp only [stepN, Function.iterate_zero, id_eq, Option.some.injEq] at h ⊢
    subst h
    simp [initConfig]
  | succ j ih =>
    intro cfgF hStepN
    rw [stepN_succ] at hStepN ⊢
    cases hprev : stepN gen (some (initConfig gen f)) j with
    | none => simp [hprev] at hStepN
    | some cfgF_prev =>
      simp only [hprev, Option.bind_some] at hStepN
      rw [ih (by omega) cfgF_prev hprev]
      simp only [Option.bind_some]
      -- step gen cfgF_prev = some cfgF
      -- Need: step gen { cfgF_prev with input := g } = some { cfgF with input := g }
      have hIdxJ := greedy_inputIndex_at_step gen hGreedy f j cfgF_prev hprev
      unfold step at hStepN ⊢
      simp only at hStepN ⊢
      have hInput : cfgF_prev.input = f :=
        reachable_input_eq ⟨j, (stepN_eq_Steps gen _ _ j).mp hprev⟩
      rw [hIdxJ, hInput] at hStepN
      have hBit : f j = g j := hAgree j (by omega)
      rw [hBit] at hStepN
      rw [hIdxJ]
      split at hStepN
      · -- gen.δ = none
        simp at hStepN
      · -- gen.δ = some val
        rename_i q' w' o itd wd hδ
        split at *
        · simp at hStepN
          have := hGreedy _ _ _ _ _ _ _ _ hδ
          simp at this
        · simp only [Option.some.injEq] at hStepN ⊢
          rw [← hStepN]

lemma greedy_computes_within_length
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (f : ℕ → Bool) (len idx : ℕ) (w : List Γo)
    (hComp : Computes gen (initConfig gen f) w)
    (k : ℕ)
    (hBound : ∀ cfg, Reachable gen (initConfig gen f) cfg → cfg.inputIndex < k)
    (hLen : len ≥ k)
    (hAgree : ∀ i, i < k → bitStringInput len idx i = f i) :
    ∃ steps, steps ≤ len ∧
      stepN gen (some (initConfig gen (bitStringInput len idx))) steps =
        some (stepNHalt gen (initConfig gen (bitStringInput len idx)) steps) ∧
      IsHalting gen (stepNHalt gen (initConfig gen (bitStringInput len idx)) steps) ∧
      (stepNHalt gen (initConfig gen (bitStringInput len idx)) steps).output = w := by
  obtain ⟨n, haltCfg, hStepN, hHalt, hOut⟩ := hComp.to_stepN
  have hSteps := (stepN_eq_Steps gen _ _ n).mp hStepN
  have hIdx_n := greedy_inputIndex_eq_steps gen hGreedy _ _ n hSteps
  simp only [initConfig, zero_add] at hIdx_n
  have hn_lt_k : n < k := by rw [← hIdx_n]; exact hBound _ ⟨n, hSteps⟩
  have hn_le_len : n ≤ len := by omega
  -- bitStringInput computation follows the same path
  have hStepN' := greedy_stepN_agree gen hGreedy f (bitStringInput len idx) n
    (fun i hi => (hAgree i (by omega)).symm) n le_rfl haltCfg hStepN
  have hHalt' : IsHalting gen { haltCfg with input := bitStringInput len idx } := by
    simp only [IsHalting, step] at hHalt ⊢
    rw [reachable_input_eq ⟨n, hSteps⟩, hIdx_n] at hHalt
    rw [hIdx_n, show bitStringInput len idx n = f n from hAgree n hn_lt_k]
    cases hδ : gen.δ haltCfg.state (f n) (haltCfg.work haltCfg.workIndex) with
    | none => simp [hδ] at hHalt ⊢
    | some val => simp [hδ] at hHalt
    --rwa [hAgree n hn_lt_k] at hHalt
  refine ⟨n, hn_le_len, ?_, ?_, ?_⟩
  · rwa [stepNHalt_eq_of_stepN gen _ _ n hStepN']
  · rw [stepNHalt_eq_of_stepN gen _ _ n hStepN']; exact hHalt'
  · rw [stepNHalt_eq_of_stepN gen _ _ n hStepN']; exact hOut

/-- Every finite input function agrees with some bitStringInput on the
    positions that matter. -/
lemma exists_bitString_for_input
    (f : ℕ → Bool) (k : ℕ) :
    ∃ len idx, len ≥ k ∧ idx < 2 ^ len ∧
      ∀ i, i < k → bitStringInput len idx i = f i := by
  refine ⟨k, ∑ i ∈ Finset.range k, if f i then 2 ^ i else 0, le_refl k, ?_, ?_⟩
  · exact sum_if_two_pow_lt f k
  · intro i hi
    simp only [bitStringInput, hi, ite_true]
    exact testBit_sum_pow f k i hi

/-- From a fresh state at (l, i), we either advance to nextEnumState or
    the enumeration returns none (found a match). -/
private lemma enum_advances_or_done (gen : Generator Γw Γo Q) (w : List Γo)
    (l i : ℕ)
    (ges : GreedyEnumState Γw Γo Q)
    (hLen : ges.currentLen = l) (hIdx : ges.currentIdx = i)
    (hRem : ges.stepsRemaining = l)
    (hInst : ges.inst = initConfig gen (bitStringInput l i)) :
    (∃ n, (fun s => s.bind (greedyEnumStep gen w))^[n] (some ges) =
      some (nextEnumState gen l i)) ∨
    (∃ n, (fun s => s.bind (greedyEnumStep gen w))^[n] (some ges) = none) := by
  -- Induct on stepsRemaining, generalizing the state
  suffices ∀ k (ges' : GreedyEnumState Γw Γo Q),
      ges'.currentLen = l → ges'.currentIdx = i →
      ges'.stepsRemaining = k → k ≤ l →
      ges'.inst = stepNHalt gen (initConfig gen (bitStringInput l i)) (l - k) →
      (∃ n, (fun s => s.bind (greedyEnumStep gen w))^[n] (some ges') =
        some (nextEnumState gen l i)) ∨
      (∃ n, (fun s => s.bind (greedyEnumStep gen w))^[n] (some ges') = none) by
    have := this l ges hLen hIdx hRem le_rfl (by rw [hInst]; simp)
    exact this
  intro k
  induction k with
  | zero =>
    intro ges' hLen' hIdx' hRem' _ hInst'
    -- stepsRemaining = 0: one greedyEnumStep either halts or times out
    have : greedyEnumStep gen w ges' =
        match step gen ges'.inst with
        | none => if ges'.inst.output = w then none
                  else some (nextEnumState gen ges'.currentLen ges'.currentIdx)
        | some _ => some (nextEnumState gen ges'.currentLen ges'.currentIdx) := by
      unfold greedyEnumStep
      cases step gen ges'.inst with
      | none => rfl
      | some cfg' => simp [hRem']
    cases hStep : step gen ges'.inst with
    | none =>
      by_cases hMatch : ges'.inst.output = w
      · right; exact ⟨1, by simp [this, hStep, hMatch]⟩
      · left; exact ⟨1, by simp [this, hStep, hMatch, hLen', hIdx']⟩
    | some cfg' =>
      left; exact ⟨1, by simp [this, hStep, hLen', hIdx']⟩
  | succ k ih =>
    intro ges' hLen' hIdx' hRem' hk hInst'
    cases hStep : step gen ges'.inst with
    | none =>
      -- Generator halted early
      by_cases hMatch : ges'.inst.output = w
      · right
        exact ⟨1, by simp [greedyEnumStep, hStep, hMatch]⟩
      · left
        exact ⟨1, by simp [greedyEnumStep, hStep, hMatch, hLen', hIdx']⟩
    | some cfg' =>
      -- Generator steps, stepsRemaining = k + 1 ≠ 0
      have hOneStep : greedyEnumStep gen w ges' =
          some { currentLen := l, currentIdx := i,
                 stepsRemaining := k,
                 inst := cfg' } := by
        unfold greedyEnumStep
        rw [hStep]
        simp [hRem', hLen', hIdx']
      have hInst'' : cfg' = stepNHalt gen (initConfig gen (bitStringInput l i)) (l - k) := by
        rw [show l - k = (l - (k + 1)) + 1 from by omega]
        simp [stepNHalt_succ, ← hInst', hStep]
      rcases ih { currentLen := l, currentIdx := i,
                  stepsRemaining := k, inst := cfg' }
          rfl rfl rfl (by omega) hInst'' with ⟨n, hn⟩ | ⟨n, hn⟩
      · left
        exact ⟨n + 1, by
          rw [Function.iterate_succ_apply]
          simp only [Option.bind_some, hOneStep]
          exact hn⟩
      · right
        exact ⟨n + 1, by
          rw [Function.iterate_succ_apply]
          simp only [Option.bind_some, hOneStep]
          exact hn⟩

/-- The enumeration eventually reaches any given (len, idx) with idx < 2^len. -/
lemma enum_reaches (gen : Generator Γw Γo Q) (w : List Γo)
    (len idx : ℕ) (hIdx : idx < 2 ^ len) :
    (∃ n ges, (fun s => s.bind (greedyEnumStep gen w))^[n]
      (some (initGreedyEnumState gen)) = some ges ∧
      ges.currentLen = len ∧ ges.currentIdx = idx ∧
      ges.stepsRemaining = len ∧
      ges.inst = initConfig gen (bitStringInput len idx)) ∨
    GreedyEnumRecognises gen w := by
  -- Prove the stronger: for all idx < 2^len, we can reach (len, idx) or done.
  suffices ∀ len idx, idx < 2 ^ len →
      (∃ n ges, (fun s => s.bind (greedyEnumStep gen w))^[n]
        (some (initGreedyEnumState gen)) = some ges ∧
        ges.currentLen = len ∧ ges.currentIdx = idx ∧
        ges.stepsRemaining = len ∧
        ges.inst = initConfig gen (bitStringInput len idx)) ∨
      GreedyEnumRecognises gen w from this len idx hIdx
  intro len
  induction len with
  | zero =>
    intro idx hIdx
    have : idx = 0 := by omega
    subst this
    left
    exact ⟨0, initGreedyEnumState gen, rfl, rfl, rfl, rfl, rfl⟩
  | succ len ihLen =>
    -- ihLen : ∀ idx, idx < 2^len → ...
    -- Now inner induction on idx
    intro idx hIdx
    induction idx with
    | zero =>
      -- Reach (len+1, 0) from (len, 2^len - 1)
      have h2pow : 2 ^ len - 1 < 2 ^ len := by omega
      rcases ihLen (2 ^ len - 1) h2pow with
        ⟨n₀, ges₀, hReach₀, hLen₀, hIdx₀, hRem₀, hInst₀⟩ | hDone
      · rcases enum_advances_or_done gen w len (2 ^ len - 1) ges₀
            hLen₀ hIdx₀ hRem₀ hInst₀ with ⟨n₁, hn₁⟩ | ⟨n₁, hn₁⟩
        · left
          have hNext : nextEnumState gen len (2 ^ len - 1) =
              { currentLen := len + 1, currentIdx := 0,
                stepsRemaining := len + 1,
                inst := initConfig gen (bitStringInput (len + 1) 0) } := by
            unfold nextEnumState
            simp [show ¬(2 ^ len - 1 + 1 < 2 ^ len) from by omega]
          refine ⟨n₁ + n₀, nextEnumState gen len (2 ^ len - 1), ?_,
            by rw [hNext], by rw [hNext], by rw [hNext], by rw [hNext]⟩
          rw [Function.iterate_add, Function.comp, hReach₀, hn₁]
        · right
          exact ⟨n₀ + n₁, by
            rw [show n₀ + n₁ = n₁ + n₀ from by omega, Function.iterate_add,
              Function.comp, hReach₀, hn₁]
          ⟩
      · right; exact hDone
    | succ idx ihIdx =>
      -- Reach (len+1, idx+1) from (len+1, idx)
      have hIdx' : idx < 2 ^ (len + 1) := by omega
      rcases ihIdx hIdx' with
        ⟨n₀, ges₀, hReach₀, hLen₀, hIdx₀, hRem₀, hInst₀⟩ | hDone
      · rcases enum_advances_or_done gen w (len + 1) idx ges₀
            hLen₀ hIdx₀ hRem₀ hInst₀ with ⟨n₁, hn₁⟩ | ⟨n₁, hn₁⟩
        · left
          have hNext : nextEnumState gen (len + 1) idx =
              { currentLen := len + 1, currentIdx := idx + 1,
                stepsRemaining := len + 1,
                inst := initConfig gen (bitStringInput (len + 1) (idx + 1)) } := by
            unfold nextEnumState
            simp [show idx + 1 < 2 ^ (len + 1) from hIdx]
          refine ⟨n₀ + n₁, nextEnumState gen (len + 1) idx, ?_,
            by rw [hNext], by rw [hNext], by rw [hNext], by rw [hNext]⟩
          rw [show n₀ + n₁ = n₁ + n₀ from by omega, Function.iterate_add,
            Function.comp, hReach₀, hn₁]
        · right
          exact ⟨n₀ + n₁, by
            rw [show n₀ + n₁ = n₁ + n₀ from by omega] at *
            rw [Function.iterate_add, Function.comp, hReach₀, hn₁]
          ⟩
      · right; exact hDone

/-- If the generator doesn't halt at any step < m, then after m iterations
    of greedyEnumStep, the state has stepNHalt at m with stepsRemaining = len - m. -/
lemma greedyEnum_steps_before_halt
    (gen : Generator Γw Γo Q) (w : List Γo) (len idx m : ℕ)
    (hm : m ≤ len)
    (hNoHalt : ∀ j, j < m → ¬IsHalting gen
      (stepNHalt gen (initConfig gen (bitStringInput len idx)) j))
    (ges : GreedyEnumState Γw Γo Q)
    (hGes : ges = { currentLen := len, currentIdx := idx,
                     stepsRemaining := len,
                     inst := initConfig gen (bitStringInput len idx) }) :
    (fun s => s.bind (greedyEnumStep gen w))^[m] (some ges) =
    some { currentLen := len, currentIdx := idx,
           stepsRemaining := len - m,
           inst := stepNHalt gen (initConfig gen (bitStringInput len idx)) m } := by
  induction m with
  | zero => simp [hGes]
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [ih (by omega) (fun j hj => hNoHalt j (by omega))]
    simp only [Option.bind_some]
    unfold greedyEnumStep
    have hNotHalt := hNoHalt m (by omega)
    unfold IsHalting at hNotHalt
    push_neg at hNotHalt
    obtain ⟨cfg', hStep⟩ := Option.ne_none_iff_exists'.mp hNotHalt
    rw [hStep]
    simp only
    have hRem : ¬(len - m = 0) := by omega
    simp [hRem]
    constructor
    · omega
    · simp [hStep]

/-- Given that the generator halts at step n, there is a first halting step m ≤ n,
    and stepNHalt at m equals stepNHalt at n. -/
lemma exists_first_halt (gen : Generator Γw Γo Q) (cfg : GenConfig Γw Γo Q) (n : ℕ)
    (hHalt : IsHalting gen (stepNHalt gen cfg n)) :
    ∃ m, m ≤ n ∧
      IsHalting gen (stepNHalt gen cfg m) ∧
      stepNHalt gen cfg m = stepNHalt gen cfg n ∧
      ∀ j, j < m → ¬IsHalting gen (stepNHalt gen cfg j) := by
  induction n with
  | zero =>
    exact ⟨0, le_refl 0, hHalt, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ n ih =>
    by_cases hPrev : ∃ m, m ≤ n ∧ IsHalting gen (stepNHalt gen cfg m)
    · obtain ⟨m, hm_le, hm_halt⟩ := hPrev
      have hHalt_n : IsHalting gen (stepNHalt gen cfg n) := by
        rw [stepNHalt_fixed gen cfg m hm_halt n hm_le]; exact hm_halt
      obtain ⟨first, hfirst_le, hfirst_halt, hfirst_eq, hfirst_min⟩ := ih hHalt_n
      refine ⟨first, by omega, hfirst_halt, ?_, hfirst_min⟩
      rw [hfirst_eq, stepNHalt_fixed gen cfg n hHalt_n (n + 1) (by omega)]
    · push_neg at hPrev
      exact ⟨n + 1, le_refl _, hHalt, rfl, fun j hj => hPrev j (by omega)⟩

/-- If the generator halts with matching output, greedyEnumStep returns none. -/
lemma greedyEnum_halt_match
    (gen : Generator Γw Γo Q) (w : List Γo) (len idx m : ℕ)
    (hHalt : IsHalting gen
      (stepNHalt gen (initConfig gen (bitStringInput len idx)) m))
    (hOut : (stepNHalt gen (initConfig gen (bitStringInput len idx)) m).output = w) :
    greedyEnumStep gen w
      { currentLen := len, currentIdx := idx,
        stepsRemaining := len - m,
        inst := stepNHalt gen (initConfig gen (bitStringInput len idx)) m } = none := by
  unfold greedyEnumStep
  rw [show step gen (stepNHalt gen (initConfig gen (bitStringInput len idx)) m) = none from hHalt]
  simp [hOut]

theorem GreedyEnumRecognises_iff_Computes
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (w : List Γo) :
    GreedyEnumRecognises gen w ↔
    ∃ input : ℕ → Bool, Computes gen (initConfig gen input) w := by
  constructor
  · -- Forward: GreedyEnumRecognises → ∃ input, Computes
    intro ⟨n, hn⟩
    suffices ∀ n ges,
        (fun s => s.bind (greedyEnumStep gen w))^[n] (some ges) = none →
        ges.inst = stepNHalt gen (initConfig gen (bitStringInput ges.currentLen ges.currentIdx))
          (ges.currentLen - ges.stepsRemaining) →
        ges.stepsRemaining ≤ ges.currentLen →
        ∃ input, Computes gen (initConfig gen input) w by
      exact this n _ hn
        (by simp [initGreedyEnumState])
        (by simp [initGreedyEnumState])
    intro n
    induction n with
    | zero => intro ges h; simp at h
    | succ n ih =>
      intro ges hn hInst hSteps
      simp only [Function.iterate_succ, Function.comp, Option.bind_some] at hn
      unfold greedyEnumStep at hn
      split at hn
      · -- generator halted (step = none)
        rename_i hStep
        split at hn
        · -- output matches: produces none
          rename_i hOut
          refine ⟨bitStringInput ges.currentLen ges.currentIdx, ?_⟩
          rw [← hOut, hInst]
          exact stepNHalt_Computes gen _ _ (by rw [← hInst]; exact hStep)
        · -- output doesn't match, advance
          rename_i hOut
          simp only [Option.bind] at hn
          apply ih _ hn
          · simp [nextEnumState, initConfig]
            split <;> simp
          · simp [nextEnumState]
            split <;> simp
      · -- generator steps (step = some cfg')
        rename_i hStep
        split at hn
        · -- stepsRemaining = 0: out of bits, advance
          rename_i hRem
          simp only [Option.bind] at hn
          apply ih _ hn
          · simp [nextEnumState, initConfig]
            split <;> simp
          · simp [nextEnumState]
            split <;> simp
        · -- stepsRemaining ≠ 0: continue stepping
          rename_i hRem
          simp only [Option.bind] at hn
          apply ih _ hn
          · simp only
            rw [show ges.currentLen - (ges.stepsRemaining - 1) =
              (ges.currentLen - ges.stepsRemaining) + 1 by omega]
            simp only [stepNHalt_succ]
            rw [show step gen (stepNHalt gen (initConfig gen
              (bitStringInput ges.currentLen ges.currentIdx))
              (ges.currentLen - ges.stepsRemaining)) = some _ from by rw [← hInst]; exact hStep]
          · simp only; omega
  · -- Backward: ∃ input, Computes → GreedyEnumRecognises
    intro ⟨f, hComp⟩
    obtain ⟨k, hBound⟩ := Computes.finite_input_reads hComp
    obtain ⟨len, idx, hLen, hIdx, hAgree⟩ := exists_bitString_for_input f k
    obtain ⟨steps, hStepsLe, _, hHalt, hOut⟩ :=
      greedy_computes_within_length gen hGreedy f len idx w hComp k hBound hLen hAgree
    -- rest proceeds exactly as before with steps ≤ len
    obtain ⟨firstHalt, hFirstLe, hFirstHalt, hFirstEq, hNoHaltBefore⟩ :=
      exists_first_halt gen (initConfig gen (bitStringInput len idx)) steps hHalt
    rcases enum_reaches gen w len idx hIdx with
      ⟨n₁, ges₁, hReach₁, hLen₁, hIdx₁, hRem₁, hInst₁⟩ | hDone
    · suffices ∃ m, (fun s => s.bind (greedyEnumStep gen w))^[m] (some ges₁) = none by
        obtain ⟨m, hm⟩ := this
        exact ⟨n₁ + m, by rw [show n₁ + m = m + n₁ from by omega,
          Function.iterate_add, Function.comp, hReach₁, hm]⟩
      have hAfterSteps := greedyEnum_steps_before_halt gen w len idx firstHalt
        (by omega) hNoHaltBefore ges₁
        (by cases ges₁; simp_all)
      have hFinalStep := greedyEnum_halt_match gen w len idx firstHalt
        hFirstHalt (by rw [hFirstEq, hOut])
      refine ⟨firstHalt + 1, ?_⟩
      change (fun s => s.bind (greedyEnumStep gen w))^[firstHalt.succ] (some ges₁) = none
      rw [Function.iterate_succ_apply']
      rw [hAfterSteps]
      simp [hFinalStep]
    · exact hDone

end GreedyEnum

end RandomisedGeneration
