import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import LeanFormalisation.Generator

namespace RandomisedGeneration

def Language (Γ : Type u)
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
 : Type u :=
  { L : Set (List Γ) // ∀ input ∈ L, default ∉ input }

def generatedLanguage {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : Language Γo :=
  ⟨{ out | ∃ input, Computes gen (initConfig gen input) out },
   fun out ⟨input, h_comp⟩ =>
     Computes.no_default gen (initConfig gen input) out h_comp (by simp [initConfig])⟩

def generableLanguages {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ] : Set (Language Γ) :=
{ L | ∃ (Γw Q : Type u) (_ : Fintype Γw) (_ : Fintype Q)
  (gen : Generator Γw Γ Q), generatedLanguage gen = L }

def languageRecognisedByTM0 {Γ Λ : Type u}
[Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) : Language Γ :=
  ⟨{ input | default ∉ input ∧ (Turing.TM0.eval M input).Dom },
   fun _ hInput => hInput.1⟩

def languagesRecognisedByTM0s {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
: Set (Language Γ) :=
  { L | ∃ (Λ : Type u) (_ : Inhabited Λ) (_ : Fintype Λ) (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)),
    L = languageRecognisedByTM0 M }

end RandomisedGeneration
