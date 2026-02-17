import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
import RandomisedGeneration.GenerationByTM0Simulation

namespace RandomisedGeneration

theorem TM0_recognisable_subset_generable {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ] :
languagesRecognisedByTM0s (Γ := Γ) ⊆ generableLanguages := by
  intro L hL
  rcases hL with ⟨Λ, hΛinh, hΛfin, M, rfl⟩
  refine ⟨Γ, ?_⟩
  refine ⟨GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨GenerationByTM0Simulation.generatorFromTM0 M, ?_⟩
  apply Subtype.ext
  exact GenerationByTM0Simulation.language_of_tm0_eq_language_of_generator_from_tm0 M

end RandomisedGeneration
