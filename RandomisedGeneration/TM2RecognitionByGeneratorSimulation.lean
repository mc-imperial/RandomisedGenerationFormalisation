import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.GreedyGeneration
import RandomisedGeneration.Language
import RandomisedGeneration.GreedyEnum.AbstractMachine
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2

namespace RandomisedGeneration

universe u

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
              GreedyEnum.clearInput, GreedyEnum.clearWorkL, GreedyEnum.clearWorkR,
              GreedyEnum.clearOutput, GreedyEnum.counter_increment,
              GreedyEnum.counter_increment_loop, GreedyEnum.counter_increment_restore,
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
