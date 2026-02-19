import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Generator

namespace RandomisedGeneration

def Language (Γ : Type u)
[Inhabited Γ] [FinEnum Γ]
 : Type u :=
  { L : Set (List Γ) // ∀ input ∈ L, default ∉ input }

def generatedLanguage {Γw Γo Q : Type u}
  [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
  (gen : Generator Γw Γo Q)
  (S : Finset Q)
  (_ : GeneratorSupports gen S) : Language Γo :=
  ⟨{ out | ∃ input, Computes gen (initConfig gen input) out },
   fun out ⟨input, h_comp⟩ =>
     Computes.no_default gen (initConfig gen input) out h_comp (by simp [initConfig])⟩

def generableLanguages {Γ : Type u}
  [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γw Q : Type u)
          (_ : Fintype Γw)
          (gen : Generator Γw Γ Q)
          (S : Finset Q)
          (hS : GeneratorSupports gen S),
    generatedLanguage gen S hS = L }

def languageRecognisedByTM0 {Γ Λ : Type u}
[Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (S : Finset Λ)
  (_ : Turing.TM0.Supports M ↑S) : Language Γ :=
  ⟨{ input | default ∉ input ∧ (Turing.TM0.eval M input).Dom },
   fun _ hInput => hInput.1⟩

def languagesRecognisedByTM0s {Γ : Type u}
[Inhabited Γ] [FinEnum Γ]
: Set (Language Γ) :=
  { L | ∃ (Λ : Type u)
          (_ : Inhabited Λ)
          (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
          (S : Finset Λ)
          (hS : Turing.TM0.Supports M S),
    L = languageRecognisedByTM0 M S hS }

end RandomisedGeneration
