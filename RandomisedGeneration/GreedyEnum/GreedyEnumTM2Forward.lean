import Mathlib
import RandomisedGeneration.GreedyEnum.AbstractMachine
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2Backward

namespace RandomisedGeneration

universe u

namespace GreedyEnum

section ForwardDirection

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]
set_option linter.unusedSectionVars false

private lemma GEStep_none_iff_label_none
    (gen : Generator Γw Γo Q)
    (cfg : GECfg Γw Γo Q) :
    GEStep gen cfg = none ↔ cfg.l = none := by
  cases cfg with
  | mk l v S =>
    cases l with
    | none => simp [GEStep, Turing.TM2.step]
    | some l => simp [GEStep, Turing.TM2.step]

private lemma copyCounterInvariant_not_halted
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hinv : CopyCounterInvariant target counter cfg) :
    GEStep gen cfg ≠ none := by
  intro h
  rw [GEStep_none_iff_label_none] at h
  rw [hinv.h_label] at h
  exact absurd h (by simp)

-- Convert ReflTransGen to iterate count
private lemma reflTransGen_to_iterate
    {α : Type*} {f : α → Option α}
    {a b : α}
    (h : Relation.ReflTransGen (fun x y => f x = some y) a b) :
    ∃ n, (fun x => x.bind f)^[n] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail x y _ hxy ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      rw [Function.iterate_succ_apply', hn, Option.bind_some, hxy]⟩

-- Iterate on none stays none
private lemma iterate_bind_none
    {α : Type*} {f : α → Option α} :
    ∀ n, (fun x => x.bind f)^[n] (none : Option α) = none
  | 0 => rfl
  | n + 1 => by rw [Function.iterate_succ_apply',
                     iterate_bind_none n]; rfl

-- Key: if halted at step n, contradiction with some at step m > n
private lemma iterate_contradiction
    {α : Type*} {f : α → Option α}
    {a b c : α} {n m : ℕ}
    (hn : (fun x => x.bind f)^[n] (some a) = some b)
    (hb : f b = none)
    (hm : (fun x => x.bind f)^[m] (some a) = some c)
    (h : n < m) : False := by
  have hpref : (fun x => x.bind f)^[m - n] (some b) = some c := by
    have : m = n + (m - n) := (Nat.add_sub_cancel' (Nat.le_of_lt h)).symm
    rw [this] at hm
    rw [show n + (m - n) = (m - n) + n from by omega] at hm
    rw [Function.iterate_add_apply, hn] at hm
    exact hm
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m - n ≠ 0)
  rw [hk_eq, Function.iterate_succ_apply] at hpref
  simp only [Option.bind_some, hb, iterate_bind_none] at hpref
  cases hpref

-- Each round of the TM2 takes at least 1 step.
-- More precisely: from CopyCounterInvariant, the first TM2 step goes to
-- a different config (since GEStep ≠ none, there exists a next config).
-- So after n rounds, the step count is ≥ n.
-- We prove this by induction, tracking both the config AND its step count.

private lemma rounds_step_count
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (hNoMatch : ∀ n,
        counterEnumStep gen stackTarget.reverse (counterIterN n) ≠ none)
    (init : GECfg Γw Γo Q)
    (hInit : CopyCounterInvariant stackTarget (counterIterN 0) init)
    (n : ℕ) :
    ∃ cfg nSteps,
      (fun x => x.bind (GEStep gen))^[nSteps] (some init) = some cfg ∧
      CopyCounterInvariant stackTarget (counterIterN n) cfg ∧
      nSteps ≥ n := by
  induction n with
  | zero => exact ⟨init, 0, rfl, hInit, le_refl 0⟩
  | succ n ih =>
    obtain ⟨cfg_n, nS_n, hIter_n, hinv_n, hn_ge⟩ := ih
    -- cfg_n has CopyCounterInvariant, so it can step
    -- From cfg_n, one full round reaches the next CopyCounterInvariant
    obtain ⟨cfg_init, hr_init, hinv_init⟩ :=
      copyCounter_to_initRun gen stackTarget
        (counterIterN n) cfg_n hinv_n
    obtain ⟨cfg_next, hr_next, hinv_next⟩ :=
      initRun_no_match_to_copyCounter gen hGreedy
        stackTarget (counterIterN n) cfg_init hinv_init
        (by
          exact hNoMatch n
        )
    -- Convert TM2Reaches from cfg_n to cfg_next to step counts
    have hreach_n_next : TM2Reaches gen cfg_n cfg_next :=
      TM2Reaches_trans hr_init hr_next
    obtain ⟨k, hk⟩ := reflTransGen_to_iterate hreach_n_next
    -- k ≥ 1 because cfg_n ≠ cfg_next (different counter values)
    have hk_pos : k ≥ 1 := by
      by_contra h
      push_neg at h
      interval_cases k
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at hk
      -- hk : some cfg_n = some cfg_next, so cfg_n = cfg_next
      have : cfg_n = cfg_next := by simpa using hk
      -- But cfg_n has counter = counterIterN n
      -- and cfg_next has counter = counterIncrement (counterIterN n)
      --   = counterIterN (n+1)
      -- These are different since counterToNat differs
      have h1 := hinv_n.h_counter
      have h2 : cfg_next.stk GreedyEnumStack.counter =
          counterIterN (n + 1) := by
        rw [counterIterN, hinv_next.h_counter]
      rw [this] at h1
      have h3 := hinv_next.h_counter
      rw [← h1] at h3
      -- counterIterN n = counterIncrement (counterIterN n)
      -- = counterIterN (n+1)
      -- counterToNat (counterIterN n) = n
      -- counterToNat (counterIterN (n+1)) = n+1
      -- n ≠ n+1, contradiction
      have := congr_arg counterToNat h3
      simp [counterToNat_increment] at this
    -- Total steps: nS_n + k
    refine ⟨cfg_next, nS_n + k, ?_, ?_, ?_⟩
    · -- iterate gives cfg_next at step nS_n + k
      rw [show nS_n + k = k + nS_n from by omega, Function.iterate_add_apply, hIter_n, hk]
    · -- CopyCounterInvariant for counterIterN (n+1)
      rwa [counterIterN]
    · -- nS_n + k ≥ n + 1
      omega

-- The forward direction
theorem tm2_halts_implies_counterEnumRecognises
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (target : List Γo)
    (hHalts : TM2Halts gen
      (Turing.TM2.init GreedyEnumStack.target target.reverse)) :
    CounterEnumRecognises gen target := by
  by_contra hNoRec
  have hNoMatch : ∀ n,
      counterEnumStep gen target (counterIterN n) ≠ none := by
    intro n habs
    exact hNoRec (iteration_reaches_none gen target n habs)
  obtain ⟨cfg_halt, hreach_halt, hhalt⟩ := hHalts
  obtain ⟨N, hN⟩ := reflTransGen_to_iterate hreach_halt
  have hInit : CopyCounterInvariant (Γw := Γw) (Q := Q) target.reverse (counterIterN 0)
      (@Turing.TM2.init GreedyEnumStack (stackAlphabet Γw Γo Q)
        GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) _ _ _
        GreedyEnumStack.target target.reverse) :=
    by simpa [counterIterN] using init_copyCounterInvariant gen target.reverse
  have hNoMatch' : ∀ n,
      counterEnumStep gen (target.reverse).reverse (counterIterN n) ≠ none := by
    simp only [List.reverse_reverse, ne_eq]
    exact hNoMatch
  obtain ⟨cfg_far, M, hM, _, hM_ge⟩ :=
    rounds_step_count gen hGreedy target.reverse hNoMatch'
      _ hInit (N + 1)
  exact iterate_contradiction hN hhalt hM (by omega)

end ForwardDirection

end GreedyEnum

end RandomisedGeneration
