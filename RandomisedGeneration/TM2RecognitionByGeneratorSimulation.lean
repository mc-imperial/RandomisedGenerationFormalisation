import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.GreedyGeneration
import RandomisedGeneration.Language
import RandomisedGeneration.GreedyEnum.AbstractMachine
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2
-- import RandomisedGeneration.Dovetailing.AbstractMachine
-- import RandomisedGeneration.Dovetailing.DovetailingTM2
-- import RandomisedGeneration.Dovetailing.GlobalInvariants
-- import RandomisedGeneration.Dovetailing.Phase1

namespace RandomisedGeneration

universe u

-- section Dovetailing

-- variable {Γw Γo Q : Type u}
-- variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]


-- set_option linter.unusedSectionVars false
-- lemma quiescentInvariant_init
--     (gen : Generator Γw Γo Q)
--     (target : List Γo) :
--     QuiescentInvariant gen target 0  (dovetailInit target) where
--   label_eq := by
--     rfl
--   counter := by
--     simp [dovetailInit, Turing.TM2.init, Function.update]
--   input := by
--     rfl
--   state := by
--     simp [dovetailInit, Turing.TM2.init, Function.update]
--   output := by
--     rfl
--   workR := by
--     rfl
--   workL := by
--     rfl
--   target_preserved := by
--     rfl
--   save_empty := by
--     simp [dovetailInit, Turing.TM2.init]

-- /-- The abstract DovetailState is "in correspondence" with a TM2 config
--     when the QuiescentInvariant holds at check_iterateInstances.
--     This is the bisimulation relation between the abstract dovetail machine
--     and the concrete TM2 implementation. -/
-- def InCorrespondence
--     (gen : Generator Γw Γo Q)
--     (target : List Γo)
--     (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
--     (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
--     : Prop :=
--   QuiescentInvariant gen target ds.instances.length tm2cfg

-- /-- The initial configs are in correspondence. -/
-- lemma inCorrespondence_init
--     (gen : Generator Γw Γo Q)
--     (target : List Γo) :
--     InCorrespondence gen target initDovetailState (dovetailInit target) := by
--   exact quiescentInvariant_init gen target

-- /-- If in correspondence and some instance has halting output matching
--     the target (reversed, due to stack ordering), the TM2 reaches a
--     halted configuration. This is the key lemma for the backward direction:
--     DovetailRecognises → TM2 halts. -/
-- lemma inCorrespondence_halt
--     (gen : Generator Γw Γo Q)
--     (target : List Γo)
--     (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
--     (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
--     (hCorr : InCorrespondence gen target ds tm2cfg)
--     (hMatch : ∃ i, i < ds.instances.length ∧
--       IsHalting gen (instanceConfig gen i ds.instances.length) ∧
--       (instanceConfig gen i ds.instances.length).output.reverse = target) :
--     ∃ tm2cfg',
--       tm2cfg'.l = none ∧
--       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
--   obtain ⟨k, hk_lt, hk_halt, hk_out⟩ := hMatch
--   let round := ds.instances.length
--   sorry -- revisit once we have quiescent_to_checkPhase again
--   -- have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
--   -- suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
--   --       DovetailLabel (DovetailSigma Γw Γo Q)),
--   --     round - j = d →
--   --     j ≤ round →
--   --     CheckPhaseInvariant gen target round j tm2cfg_j →
--   --     Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
--   --     (∃ i, i < round - j ∧
--   --       IsHalting gen (instanceConfig gen i round) ∧
--   --       (instanceConfig gen i round).output.reverse = target) →
--   --     ∃ tm2cfg',
--   --       tm2cfg'.l = none ∧
--   --       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' by
--   --   exact this round 0 tm2cfg (by omega) (Nat.zero_le _) hCheck₀
--   --     Relation.ReflTransGen.refl ⟨k, by omega, hk_halt, hk_out⟩
--   -- intro d
--   -- induction d with
--   -- | zero =>
--   --   intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, _, _⟩
--   --   omega
--   -- | succ d ih =>
--   --   intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, hi_halt, hi_out⟩
--   --   -- The next instance to check is round - 1 - j
--   --   by_cases hMatch_j : IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
--   --       (instanceConfig gen (round - 1 - j) round).output.reverse = target
--   --   · have hj_lt : j < round := by omega
--   --     obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
--   --       checkPhase_halt_on_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
--   --     exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_j h_reaches'⟩
--   --   · have hj_lt : j < round := by omega
--   --     obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
--   --       checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
--   --     have hi_ne : i ≠ round - 1 - j := by
--   --       intro heq; rw [heq] at hi_halt hi_out; exact hMatch_j ⟨hi_halt, hi_out⟩
--   --     exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
--   --       (Relation.ReflTransGen.trans hReach_j hReach_next)
--   --       ⟨i, by omega, hi_halt, hi_out⟩

-- /-- From CheckPhaseInvariant with all instances checked (j = round) and no match,
--     restoring save stacks reaches spawn_copyCounter with QuiescentInvariant. -/
-- lemma checkPhase_complete_to_pushNewConfig
--     (gen : Generator Γw Γo Q)
--     (target : List Γo)
--     (round : ℕ)
--     (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
--     (hInv : CheckPhaseInvariant gen target round round tm2cfg) :
--     ∃ tm2cfg',
--       QuiescentInvariant gen target round tm2cfg' ∧
--       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
--   sorry -- TODO - reconsider this. QuiescentInvariant I think now just applies to the start of a round.

-- /-- From spawn_copyCounter, spawn a new instance and step all,
--     reaching check_iterateInstances at round+1. -/
-- lemma pushNewConfig_step_to_next_check_iterateInstances
--     (gen : Generator Γw Γo Q)
--     (target : List Γo)
--     (round : ℕ)
--     (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
--     (hInv : QuiescentInvariant gen target round tm2cfg) :
--     ∃ tm2cfg',
--       QuiescentInvariant gen target (round + 1) tm2cfg' ∧
--       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
--   sorry -- Needs work - the two QuiescentInvariants are meant to refer to different things here; one at the start and one after checking is done.

-- /-- If in correspondence and no instance matches, one abstract dovetailStep
--     corresponds to finitely many TM2 steps, reaching a new correspondence.
--     This is the simulation lemma: one abstract round = one concrete round. -/
-- lemma inCorrespondence_step
--     (gen : Generator Γw Γo Q)
--     (target : List Γo)
--     (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
--     (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
--     (hCorr : InCorrespondence gen target ds tm2cfg)
--     (hNoMatch : ∀ i, i < ds.instances.length →
--       ¬(IsHalting gen (instanceConfig gen i ds.instances.length) ∧
--         (instanceConfig gen i ds.instances.length).output.reverse = target)) :
--     ∃ tm2cfg',
--       InCorrespondence gen target (dovetailStep gen ds) tm2cfg' ∧
--       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
--   let round := ds.instances.length
--   sorry -- REVISIT
--   -- Phase 1: Check all instances, find no match, advance to j = round
--   -- have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
--   -- have hCheckAll : ∃ tm2cfg_check,
--   --     CheckPhaseInvariant gen target round round tm2cfg_check ∧
--   --     Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check := by
--   --   suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
--   --         DovetailLabel (DovetailSigma Γw Γo Q)),
--   --       round - j = d →
--   --       j ≤ round →
--   --       CheckPhaseInvariant gen target round j tm2cfg_j →
--   --       Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
--   --       ∃ tm2cfg_check,
--   --         CheckPhaseInvariant gen target round round tm2cfg_check ∧
--   --         Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check by
--   --     exact this round 0 tm2cfg rfl (Nat.zero_le _) hCheck₀ Relation.ReflTransGen.refl
--   --   intro d
--   --   induction d with
--   --   | zero =>
--   --     intro j tm2cfg_j hd hj hInv_j hReach_j
--   --     have : j = round := by omega
--   --     subst this
--   --     exact ⟨tm2cfg_j, hInv_j, hReach_j⟩
--   --   | succ d ih =>
--   --     intro j tm2cfg_j hd hj hInv_j hReach_j
--   --     have hj_lt : j < round := by omega
--   --     -- Instance round-1-j doesn't match (from hNoMatch)
--   --     have hNoMatch_j : ¬(IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
--   --         (instanceConfig gen (round - 1 - j) round).output.reverse = target) :=
--   --       hNoMatch (round - 1 - j) (by omega)
--   --     obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
--   --       checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hNoMatch_j
--   --     exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
--   --       (Relation.ReflTransGen.trans hReach_j hReach_next)
--   -- -- Phase 2: From CheckPhaseInvariant at j=round, restore to pushNewConfig
--   -- obtain ⟨tm2cfg_check, hInv_check, hReach_check⟩ := hCheckAll
--   -- obtain ⟨tm2cfg_push, hInv_push, hReach_push⟩ :=
--   --   checkPhase_complete_to_pushNewConfig gen target round tm2cfg_check hInv_check
--   -- -- Phase 3: From pushNewConfig, spawn + step + restore + increment to next check_iterateInstances
--   -- obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
--   --   pushNewConfig_step_to_next_check_iterateInstances gen target round tm2cfg_push hInv_push
--   -- -- Connect everything
--   -- refine ⟨tm2cfg_next, ?_, ?_⟩
--   -- · -- InCorrespondence gen target (dovetailStep gen ds) tm2cfg_next
--   --   -- This is QuiescentInvariant gen target (round+1) check_iterateInstances tm2cfg_next
--   --   -- which is hInv_next, but we need to show round+1 = (dovetailStep gen ds).instances.length
--   --   change QuiescentInvariant gen target (dovetailStep gen ds).instances.length
--   --     DovetailLabel.check_iterateInstances tm2cfg_next
--   --   rw [show (dovetailStep gen ds).instances.length = round + 1 from by
--   --     simp [dovetailStep, round]]
--   --   exact hInv_next
--   -- · exact Relation.ReflTransGen.trans
--   --     (Relation.ReflTransGen.trans hReach_check hReach_push) hReach_next

-- lemma dovetailTM2_halts_implies_DovetailRecognises
--     (gen : Generator Γw Γo Q)
--     (w : List Γo) :
--     (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom →
--     DovetailRecognises gen w.reverse := by
--   -- One idea is to prove this by contrapositive.
--   sorry

-- /-- Backward: if DovetailRecognises, then the TM2 halts. -/
-- lemma DovetailRecognises_implies_dovetailTM2_halts
--     (gen : Generator Γw Γo Q)
--     (w : List Γo) :
--     DovetailRecognises gen w.reverse →
--     (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom := by
--   intro ⟨n, i, cfg, h_inst, h_halt, h_out⟩
--   suffices ∃ tm2cfg' : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
--         DovetailLabel (DovetailSigma Γw Γo Q),
--       tm2cfg'.l = none ∧
--       Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
--         (dovetailInit w) tm2cfg' by
--     obtain ⟨tm2cfg', h_halt', h_reaches⟩ := this
--     rw [Turing.TM2.eval, Part.dom_iff_mem]
--     have h_halt_step : Turing.TM2.step (dovetailMachine gen) tm2cfg' = none := by
--       cases tm2cfg'; simp_all [Turing.TM2.step]
--     exact ⟨tm2cfg'.stk DovetailStack.target,
--       Part.mem_map _ (Turing.mem_eval.mpr ⟨h_reaches, h_halt_step⟩)⟩
--   suffices ∀ r,
--       ∃ (tm2cfg_r : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
--             DovetailLabel (DovetailSigma Γw Γo Q)),
--         (tm2cfg_r.l = none ∨
--          InCorrespondence gen w
--            ((dovetailStep gen)^[r] initDovetailState) tm2cfg_r) ∧
--         Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
--           (dovetailInit w) tm2cfg_r by
--     obtain ⟨tm2cfg_n, hAlt, hReach_n⟩ := this n
--     rcases hAlt with h_halt' | hCorr_n
--     · exact ⟨tm2cfg_n, h_halt', hReach_n⟩
--     · have hi : i < n := by
--         by_contra h; push_neg at h
--         exact absurd h_inst (by
--           rw [List.getElem?_eq_none (by rw [instances_length_after_steps]; omega)]
--           exact Option.some_ne_none _ ∘ Eq.symm)
--       have hMatch : ∃ j,
--           j < ((dovetailStep gen)^[n] initDovetailState).instances.length ∧
--           IsHalting gen (instanceConfig gen j
--             ((dovetailStep gen)^[n] initDovetailState).instances.length) ∧
--           (instanceConfig gen j
--             ((dovetailStep gen)^[n] initDovetailState).instances.length).output.reverse = w := by
--         rw [instances_length_after_steps]
--         refine ⟨i, hi, ?_⟩
--         rw [instance_config_after_steps gen n i hi] at h_inst
--         have h_eq := Option.some.inj h_inst
--         rw [← h_eq] at h_halt h_out
--         exact ⟨h_halt, by simp only [instanceConfig]; rw [h_out, List.reverse_reverse]⟩
--       obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
--         inCorrespondence_halt gen w _ tm2cfg_n hCorr_n hMatch
--       exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_n h_reaches'⟩
--   intro r
--   induction r with
--   | zero =>
--     exact ⟨dovetailInit w, Or.inr (inCorrespondence_init gen w),
--       Relation.ReflTransGen.refl⟩
--   | succ r ih =>
--     obtain ⟨tm2cfg_r, hAlt_r, hReach_r⟩ := ih
--     rcases hAlt_r with h_halt_r | hCorr_r
--     · exact ⟨tm2cfg_r, Or.inl h_halt_r, hReach_r⟩
--     · by_cases hMatch_r : ∃ j,
--           j < ((dovetailStep gen)^[r] initDovetailState).instances.length ∧
--           IsHalting gen (instanceConfig gen j
--             ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
--           (instanceConfig gen j
--             ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse = w
--       · obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
--           inCorrespondence_halt gen w _ tm2cfg_r hCorr_r hMatch_r
--         exact ⟨tm2cfg', Or.inl h_halt', Relation.ReflTransGen.trans hReach_r h_reaches'⟩
--       · push_neg at hMatch_r
--         have hNoMatch : ∀ j,
--             j < ((dovetailStep gen)^[r] initDovetailState).instances.length →
--             ¬(IsHalting gen (instanceConfig gen j
--                 ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
--               (instanceConfig gen j
--                 ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse
--                 = w) := by
--           intro j hj ⟨hHalt, hOut⟩
--           exact hMatch_r j hj hHalt hOut
--         obtain ⟨tm2cfg_next, hCorr_next, hReach_next⟩ :=
--           inCorrespondence_step gen w _ tm2cfg_r hCorr_r hNoMatch
--         rw [show (dovetailStep gen)^[r + 1] initDovetailState =
--             dovetailStep gen ((dovetailStep gen)^[r] initDovetailState) from
--           by rw [Function.iterate_succ', Function.comp_apply]]
--         exact ⟨tm2cfg_next, Or.inr hCorr_next,
--           Relation.ReflTransGen.trans hReach_r hReach_next⟩

-- /-- The dovetail TM2 halts on input w iff DovetailRecognises gen w.reverse. -/
-- theorem dovetailTM2_halts_iff_DovetailRecognises
--     (gen : Generator Γw Γo Q)
--     (w : List Γo) :
--     (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom ↔
--     DovetailRecognises gen w.reverse :=
--   ⟨dovetailTM2_halts_implies_DovetailRecognises gen w,
--    DovetailRecognises_implies_dovetailTM2_halts gen w⟩

-- set_option linter.unusedSectionVars true
-- end Dovetailing

/-- The TM2 machine halts iff the abstract greedy enumeration reaches none. -/
theorem greedyEnumTM2_halts_iff_GreedyEnumRecognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    (Turing.TM2.eval (GreedyEnum.greedyEnumMachine gen)
      GreedyEnum.GreedyEnumStack.target target).Dom ↔
    GreedyEnum.GreedyEnumRecognises gen target.reverse := by
  sorry

-- The greedy enum TM2 halts on input `target` iff `target` is computed by
-- the generator on some input (for a greedy generator).
theorem greedyEnumMachine_recognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (target : List Γo) :
    (Turing.TM2.eval (GreedyEnum.greedyEnumMachine gen)
      GreedyEnum.GreedyEnumStack.target target.reverse).Dom ↔
    target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
  rw [greedyEnumTM2_halts_iff_GreedyEnumRecognises]
  simp only [List.reverse_reverse]
  rw [GreedyEnum.GreedyEnumRecognises_iff_Computes gen hGreedy]
  simp only [generatedLanguage, Set.mem_setOf_eq]

-- -- The dovetail   TM2 halts on input `target` iff `target` is in the generated language.
-- theorem dovetailMachine_recognises {Γw Γo Q : Type u}
--     [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
--     (gen : Generator Γw Γo Q)
--     (target : List Γo) :
--     (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target target.reverse).Dom ↔
--     target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
--   rw [dovetailTM2_halts_iff_DovetailRecognises]
--   simp only [List.reverse_reverse]
--   rw [DovetailRecognises_iff_Computes]
--   simp only [generatedLanguage, Set.mem_setOf_eq]

lemma every_generable_language_is_tm2_recognisable
    {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ generableLanguages) :
    L ∈ languagesRecognisedByTM2s := by
  -- Step 1: Extract the generator
  obtain ⟨Γw, Q, hΓwfinenum, hQdec, gen, S_gen, hS_gen, hgen⟩ := hL
  haveI : DecidableEq Q := hQdec
  -- Step 2: Greedify, then restrict
  let ggen := gen.greedify
  let S_ggen := S_gen ×ˢ (Finset.univ : Finset (Option Bool))
  have hS_ggen : GeneratorSupports ggen S_ggen := GeneratorSupports_greedify gen S_gen hS_gen
  have hGreedy : ggen.IsGreedy := gen.greedify_isGreedy
  have hLang : generatedLanguage gen S_gen hS_gen = generatedLanguage ggen S_ggen hS_ggen :=
    generatedLanguage_greedify gen S_gen hS_gen
  let gen' := ggen.restrictToSupport S_ggen hS_ggen
  haveI : Fintype ↥S_ggen := inferInstance
  haveI : DecidableEq ↥S_ggen := inferInstance
  haveI : FinEnum ↥S_ggen := FinEnum.ofList (Finset.univ.val.toList) (by simp)
  haveI : Inhabited ↥S_ggen := ⟨gen'.init⟩
  haveI : Inhabited Γw := ⟨gen.blank⟩
  haveI : ∀ k, Inhabited (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  haveI : ∀ k, Fintype (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  haveI : ∀ k, DecidableEq (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  -- Step 3: gen' is also greedy
  have hGreedy' : gen'.IsGreedy :=
    Generator.restrictToSupport_isGreedy ggen S_ggen hS_ggen hGreedy
  refine ⟨
    GreedyEnum.GreedyEnumStack,
    inferInstance, inferInstance, inferInstance,
    GreedyEnum.stackAlphabet Γw Γ ↥S_ggen,
    inferInstance, inferInstance, inferInstance, rfl,
    GreedyEnum.GreedyEnumLabel,
    inferInstance, inferInstance,
    GreedyEnum.GreedyEnumSigma Γw Γ ↥S_ggen,
    inferInstance, inferInstance,
    GreedyEnum.greedyEnumMachine gen',
    Finset.univ,
    ⟨Finset.mem_univ _, fun q _ => by
      cases q <;> simp only [GreedyEnum.greedyEnumMachine,
              GreedyEnum.copyCounter, GreedyEnum.copyCounter_restore, GreedyEnum.initRun,
              GreedyEnum.runStep, GreedyEnum.runStep_apply, GreedyEnum.runStep_moveHead,
              GreedyEnum.checkOutput, GreedyEnum.checkOutput_restoreTarget,
              GreedyEnum.clearInput, GreedyEnum.clearWorkL, GreedyEnum.clearWorkR, GreedyEnum.clearOutput,
              GreedyEnum.counter_increment, GreedyEnum.counter_increment_loop, GreedyEnum.counter_increment_restore,
              Turing.TM2.SupportsStmt] <;>
            simp (config := { decide := true })
      ⟩,
    ?_⟩
  subst hgen
  ext input
  simp only [Set.mem_setOf_eq]
  have lang_eq : generatedLanguage gen S_gen hS_gen =
      generatedLanguage gen' Finset.univ (generator_supports_univ gen') := by
    rw [hLang]
    ext w
    simp only [generatedLanguage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes ggen S_ggen hS_ggen h⟩
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes_lift ggen S_ggen hS_ggen h⟩
  rw [lang_eq]
  exact (greedyEnumMachine_recognises gen' hGreedy' input).symm

end RandomisedGeneration
