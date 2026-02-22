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
    rcases hL with ⟨Γ', hΓ'inh, hΓ'fin, hΓ'deceq, enc, henc_inj, henc_blank, Λ, hΛinh,
      M, S, hS, hLeq⟩
    refine ⟨Γ', GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), inferInstance,
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
  obtain ⟨Γw, Q, hΓw, gen, S_gen, hS_gen, hgen⟩ := hL
  sorry
  -- exact every_tm1_recognisable_language_is_tm0_recognisable _
  --   (hgen ▸ generable_language_is_tm1_recognisable gen S_gen hS_gen)

theorem tm0_recognisable_eq_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  languagesRecognisedByTM0s (Γ := Γ) = generableLanguages := by
  apply Set.Subset.antisymm
  · exact tm0_recognisable_subset_generable
  · exact generable_subset_tm0_recognisable

end RandomisedGeneration
