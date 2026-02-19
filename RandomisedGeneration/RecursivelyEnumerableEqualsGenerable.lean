import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
import RandomisedGeneration.GenerationByTM0Simulation

namespace RandomisedGeneration

theorem TM0_recognisable_subset_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  languagesRecognisedByTM0s (Γ := Γ) ⊆ generableLanguages := by
    intro L hL
    rcases hL with ⟨Λ, hΛinh, M, S, hS, rfl⟩
    refine ⟨Γ, ?_⟩
    refine ⟨GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), ?_⟩
    refine ⟨inferInstance, ?_⟩
    refine ⟨GenerationByTM0Simulation.generatorFromTM0 M, ?_⟩
    refine ⟨(GenerationByTM0Simulation.generatorFromTM0_supports M S hS).choose, ?_⟩
    refine ⟨(GenerationByTM0Simulation.generatorFromTM0_supports M S hS).choose_spec, ?_⟩
    apply Subtype.ext
    exact GenerationByTM0Simulation.language_of_tm0_eq_language_of_generator_from_tm0 M S hS

end RandomisedGeneration
