import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

def languageRecognisedByTM2 {K : Type u} {Γ : K → Type u} {Λ σ : Type u}
[Fintype Λ] [Fintype σ] [Fintype K]
[Inhabited Λ] [Inhabited σ] [DecidableEq K]
[∀ k, Inhabited (Γ k)] [∀ k, Fintype (Γ k)] [∀ k, FinEnum (Γ k)] [∀ k, DecidableEq (Γ k)]
(k : K)
(M : Λ → Turing.TM2.Stmt Γ Λ σ) : Language (Γ k) :=
  ⟨{ input | default ∉ input ∧ (Turing.TM2.eval M k input).Dom },
   fun _ hInput => hInput.1⟩

def languageRecognisedByTM1 {Γ Λ σ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
[Inhabited Λ] [Inhabited σ]
(M : Λ → Turing.TM1.Stmt Γ Λ σ) : Language Γ :=
  ⟨{ input | default ∉ input ∧ (Turing.TM1.eval M input).Dom },
   fun _ hInput => hInput.1⟩

theorem anything_a_generator_generates_can_be_recognised_by_a_tm2
{Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  (output : List Γo)
  (h_no_default : default ∉ output) :
  output ∈ (generatedLanguage gen).val →
  -- TODO: Replace (fun _ : ULift Unit => Γo) and default with the concrete stack index type
  -- and output stack index once the TM2 simulation is built.
  ∃ (Λ σ : Type u) (_ : Inhabited Λ) (_ : Inhabited σ)
    (M : Λ → Turing.TM2.Stmt (fun _ : ULift.{u} Unit => Γo) Λ σ),
    output ∈ (languageRecognisedByTM2 (Γ := fun _ : ULift.{u} Unit => Γo) default M).val := by
  -- TODO: Hard proof - simulate gen with a TM2 via dovetailing over input bitstreams
  sorry

theorem anything_a_generator_generates_can_be_recognised_by_a_tm1
{Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  (output : List Γo)
  (h_no_default : default ∉ output) :
  output ∈ (generatedLanguage gen).val →
  ∃ (Γ' Λ σ : Type u)
    (_ : Inhabited Γ') (_ : Fintype Γ') (_ : FinEnum Γ') (_ : DecidableEq Γ')
    (_ : Inhabited Λ) (_ : Inhabited σ)
    (M : Λ → Turing.TM1.Stmt Γ' Λ σ)
    (input : List Γ'),
    default ∉ input ∧ (Turing.TM1.eval M input).Dom := by
  intro h
  obtain ⟨Λ₂, σ₂, hΛ₂, hσ₂, M₂, hM₂⟩ :=
    anything_a_generator_generates_can_be_recognised_by_a_tm2 gen output h_no_default h
  haveI : DecidableEq (Turing.TM2to1.Γ' (ULift.{u} Unit) (fun _ => Γo)) := by sorry
  haveI : FinEnum (Turing.TM2to1.Γ' (ULift.{u} Unit) (fun _ => Γo)) :=
    by sorry
  refine ⟨
    Turing.TM2to1.Γ' (ULift.{u} Unit) (fun _ => Γo),
    Turing.TM2to1.Λ' (ULift.{u} Unit) (fun _ => Γo) Λ₂ σ₂,
    σ₂,
    inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hσ₂,
    Turing.TM2to1.tr M₂,
    Turing.TM2to1.trInit (ULift.up ()) output,
    ?_, ?_⟩
  · -- TODO: show default ∉ trInit (ULift.up ()) output
    sorry
  · exact (Turing.TM2to1.tr_eval_dom M₂ (ULift.up ()) output).mpr hM₂.2

theorem anything_a_generator_generates_can_be_recognised_by_a_tm0
{Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  (output : List Γo)
  (h_no_default : default ∉ output) :
output ∈ (generatedLanguage gen).val →
∃ (Λ : Type u) (_ : Inhabited Λ) (_ : Fintype Λ) (M : Turing.TM0.Machine Γo Λ),
  output ∈ (languageRecognisedByTM0 M).val := by
-- Proof: invoke anything_a_generator_generates_can_be_recognised_by_a_tm1 and then use the TM2 -> TM1 conversion
  sorry

end RandomisedGeneration
