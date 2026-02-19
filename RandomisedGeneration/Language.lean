import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
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

def languagesRecognisedByTM0s {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γ' : Type u)
          (_ : Inhabited Γ')
          (_ : Fintype Γ')
          (_ : DecidableEq Γ')
          (enc : Γ → Γ')
          (_ : Function.Injective enc)
          (_ : enc default = default)
          (Λ : Type u)
          (_ : Inhabited Λ)
          (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
          (S : Finset Λ)
          (_ : Turing.TM0.Supports M S),
    L.val = { input | default ∉ input ∧ (Turing.TM0.eval M (input.map enc)).Dom } }

def languagesRecognisedByTM1s {Γ : Type u} [Inhabited Γ] [FinEnum Γ] : Set (Language Γ) :=
  { L | ∃ (Γ' : Type u)
          (_ : Inhabited Γ')
          (_ : Fintype Γ')
          (_ : DecidableEq Γ')
          (enc : Γ → Γ')
          (_ : Function.Injective enc)
          (_ : enc default = default)
          (Λ : Type u)
          (_ : Inhabited Λ)
          (σ : Type u)
          (_ : Inhabited σ)
          (_ : Fintype σ)
          (M : Λ → Turing.TM1.Stmt Γ' Λ σ)
          (S : Finset Λ)
          (_ : Turing.TM1.Supports M S),
        L.val = { input | default ∉ input ∧ (Turing.TM1.eval M (input.map enc)).Dom } }

lemma every_tm1_recognisable_language_is_tm0_recognisable {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ languagesRecognisedByTM1s) :
    L ∈ languagesRecognisedByTM0s := by
  obtain ⟨Γ', hΓ'inh, hΓ'fin, hΓ'dec, enc, henc_inj, henc_def, Λ,
    hΛinh, σ, hσinh, hσfin, M, S, hS, hL_eq⟩ := hL
  refine ⟨Γ', hΓ'inh, hΓ'fin, hΓ'dec, enc, henc_inj, henc_def,
          Turing.TM1to0.Λ' M, inferInstance,
          Turing.TM1to0.tr M,
          Turing.TM1to0.trStmts M S,
          Turing.TM1to0.tr_supports M hS,
          ?_⟩
  rw [hL_eq]
  ext input
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnodef, hdom⟩
    exact ⟨hnodef, (Turing.TM1to0.tr_eval M (input.map enc)) ▸ hdom⟩
  · rintro ⟨hnodef, hdom⟩
    exact ⟨hnodef, (Turing.TM1to0.tr_eval M (input.map enc)) ▸ hdom⟩

end RandomisedGeneration
