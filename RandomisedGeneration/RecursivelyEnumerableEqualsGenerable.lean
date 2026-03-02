import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
import RandomisedGeneration.GenerationByTM0Simulation
import RandomisedGeneration.TM2RecognitionByGeneratorSimulation

namespace RandomisedGeneration

theorem tm0_recognisable_subset_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  languagesRecognisedByTM0s (Γ := Γ) ⊆ generableLanguages := by
  intro L hL
  obtain ⟨Γ', hΓ'inh, Γ'finenum, enc, henc_inj, henc_blank, Λ, hΛinh, hΛdec, M, S, hS, hLeq⟩ := hL
  haveI : FinEnum Γ' := FinEnum.ofList (Finset.univ.val.toList) (by simp)
  haveI : DecidableEq Λ := hΛdec
  refine ⟨Γ', GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), inferInstance,
          inferInstance,
          GenerationByTM0Simulation.generatorFromTM0 enc M,
          (GenerationByTM0Simulation.generatorFromTM0_supports enc M S hS).choose,
          (GenerationByTM0Simulation.generatorFromTM0_supports enc M S hS).choose_spec, ?_⟩
  rw [hLeq]
  exact GenerationByTM0Simulation.language_of_tm0_eq_language_of_generator_from_tm0
    enc henc_blank M S hS

theorem generable_subset_tm0_recognisable {Γo : Type u}
    [Inhabited Γo] [FinEnum Γo] :
    generableLanguages (Γ := Γo) ⊆ languagesRecognisedByTM0s (Γ := Γo) := by
  intro L hL
  exact every_tm1_recognisable_language_is_tm0_recognisable L
    (every_tm2_recognisable_language_is_tm1_recognisable L
      (every_generable_language_is_tm2_recognisable L hL))

theorem tm0_recognisable_eq_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  languagesRecognisedByTM0s (Γ := Γ) = generableLanguages := by
  apply Set.Subset.antisymm
  · exact tm0_recognisable_subset_generable
  · exact generable_subset_tm0_recognisable

end RandomisedGeneration
