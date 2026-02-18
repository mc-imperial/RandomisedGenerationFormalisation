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
[Fintype Γw]
[Inhabited Γo] [FinEnum Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : Language Γo :=
  ⟨{ out | ∃ input, Computes gen (initConfig gen input) out },
   fun out ⟨input, h_comp⟩ =>
     Computes.no_default gen (initConfig gen input) out h_comp (by simp [initConfig])⟩

def generableLanguages {Γ : Type u}
[Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
{ L | ∃ (Γw Q : Type u) (_ : Fintype Γw) (_ : Fintype Q)
  (gen : Generator Γw Γ Q), generatedLanguage gen = L }

-- Does not require Fintype Λ so that the Generator → TM0 direction can use it
def languageRecognisedByTM0 {Γ Λ : Type u}
[Inhabited Λ] [Fintype Λ] [Inhabited Γ] [FinEnum Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) : Language Γ :=
  ⟨{ input | default ∉ input ∧ (Turing.TM0.eval M input).Dom },
   fun _ hInput => hInput.1⟩

-- Requires Fintype Λ so that TM0 → Generator direction can use generatorFromTM0
def languagesRecognisedByTM0s {Γ : Type u}
[Inhabited Γ] [FinEnum Γ]
: Set (Language Γ) :=
  { L | ∃ (Λ : Type u) (_ : Inhabited Λ) (_ : Fintype Λ) (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)),
    L = languageRecognisedByTM0 M }

-- The weak version without Fintype Λ, needed for the generable → TM0 direction
def languagesRecognisedByTM0s_weak {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
: Set (Language Γ) :=
  { L | ∃ (Λ : Type u) (_ : Inhabited Λ) (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)),
    L = languageRecognisedByTM0 M }

-- The two sets are equal: Fintype on the state space doesn't affect recognisability
-- This is the key mathematical fact that lets us connect the two directions
theorem languagesRecognisedByTM0s_eq_weak {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ] :
languagesRecognisedByTM0s (Γ := Γ) = languagesRecognisedByTM0s_weak (Γ := Γ) := by
  apply Set.Subset.antisymm
  · -- Strong → Weak: trivial, just drop Fintype
    intro L ⟨Λ, hΛinh, _, M, hM⟩
    exact ⟨Λ, hΛinh, M, hM⟩
  · -- Weak → Strong: hard, need to show any TM0 with infinite states
    -- can be simulated by one with finite states via Supports
    sorry

end RandomisedGeneration
