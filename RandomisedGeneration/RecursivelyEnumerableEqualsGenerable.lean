import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
import RandomisedGeneration.GenerationByTM0Simulation
import RandomisedGeneration.TM2RecognitionByGeneratorSimulation

namespace RandomisedGeneration

theorem TM0_recognisable_subset_generable {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] :
  languagesRecognisedByTM0s (Γ := Γ) ⊆ generableLanguages := by
    intro L hL
    rcases hL with ⟨Γ', hΓ'inh, hΓ'fin, hΓ'deceq, enc, henc_inj, henc_default, Λ, hΛinh,
      M, S, hS, hLeq⟩
    refine ⟨Γ', GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), inferInstance,
           GenerationByTM0Simulation.generatorFromTM0 enc M,
           (GenerationByTM0Simulation.generatorFromTM0_supports enc M S hS).choose,
           (GenerationByTM0Simulation.generatorFromTM0_supports enc M S hS).choose_spec, ?_⟩
    apply Subtype.ext
    rw [hLeq]
    exact GenerationByTM0Simulation.language_of_tm0_eq_language_of_generator_from_tm0
      enc henc_default henc_inj M S hS

end RandomisedGeneration
