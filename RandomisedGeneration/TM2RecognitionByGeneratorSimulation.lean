import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

-- The stack index type for our dovetailing TM2
inductive DovetailStack
  | currentInput
  | candidate
  | target
  deriving DecidableEq

@[reducible]
def dovetailStackAlph (Γo : Type u) : DovetailStack → Type u
  | DovetailStack.currentInput => ULift Bool
  | DovetailStack.candidate    => Γo
  | DovetailStack.target       => Γo

def DovetailState (Γw Γo Q : Type u) : Type u := sorry

def DovetailSigma (Γw Γo Q : Type u) : Type u := sorry

instance (Γw Γo Q : Type u) : Inhabited (DovetailState Γw Γo Q) := sorry

instance (Γw Γo Q : Type u) : Inhabited (DovetailSigma Γw Γo Q) := sorry

instance (Γw Γo Q : Type u) : Fintype (DovetailSigma Γw Γo Q) := sorry

def tm2FromGenerator
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    DovetailState Γw Γo Q →
    Turing.TM2.Stmt (dovetailStackAlph Γo) (DovetailState Γw Γo Q) (DovetailSigma Γw Γo Q) :=
  sorry

def tm2FromGeneratorSupport
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    Finset (DovetailState Γw Γo Q) :=
  sorry

theorem tm2FromGeneratorSupported
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Supports (tm2FromGenerator gen) (tm2FromGeneratorSupport gen) :=
  sorry

-- def languageRecognisedByTM2 {Λ σ : Type u} {Γ : DovetailStack → Type u}
--     [Inhabited (Γ DovetailStack.target)] [FinEnum (Γ DovetailStack.target)]
--     [Inhabited Λ] [Inhabited σ] [Fintype σ]
--     (M : Λ → Turing.TM2.Stmt Γ Λ σ)
--     (S : Finset Λ)
--     (_ : Turing.TM2.Supports M S) : Language (Γ DovetailStack.target) :=
--   ⟨{ input | default ∉ input ∧ (Turing.TM2.eval M DovetailStack.target input).Dom },
--    fun _ hInput => hInput.1⟩

-- theorem tm2FromGenerator_correct
--     {Γw Γo Q : Type u}
--     [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
--     (gen : Generator Γw Γo Q)
--     (S_gen : Finset Q)
--     (hS_gen : GeneratorSupports gen S_gen) :
--     languageRecognisedByTM2 (tm2FromGenerator gen)
--       (tm2FromGeneratorSupport gen)
--       (tm2FromGeneratorSupported gen) =
--       generatedLanguage gen S_gen hS_gen :=
--   sorry

lemma generable_language_is_tm1_recognisable {Γo : Type u}
    [Inhabited Γo] [FinEnum Γo]
    {Γw Q : Type u} [Fintype Γw]
    (gen : Generator Γw Γo Q)
    (S_gen : Finset Q)
    (hS_gen : GeneratorSupports gen S_gen) :
    generatedLanguage gen S_gen hS_gen ∈ languagesRecognisedByTM1s (Γ := Γo) := by
  -- refine ⟨Turing.TM2to1.Γ' DovetailStack (dovetailStackAlph Γo),
  --         inferInstance, inferInstance, inferInstance,
  --         fun a => (false, fun _ => some a),
  --         fun a b h => by simp [Function.funext_iff] at h; exact h DovetailStack.target,
  --         by simp [Set.mem_range]; intro a; simp [Prod.ext_iff],
  --         Turing.TM2to1.Λ' DovetailStack (dovetailStackAlph Γo)
  --           (DovetailState Γw Γo Q) (DovetailSigma Γw Γo Q),
  --         inferInstance,
  --         DovetailSigma Γw Γo Q,
  --         inferInstance, inferInstance,
  --         Turing.TM2to1.tr (tm2FromGenerator gen),
  --         Turing.TM2to1.trSupp (tm2FromGenerator gen) (tm2FromGeneratorSupport gen),
  --         Turing.TM2to1.tr_supports (tm2FromGenerator gen) (tm2FromGeneratorSupported gen),
  --         ?_⟩
  -- need to show generatedLanguage gen S_gen hS_gen =
  --   { input | (TM1.eval (TM2to1.tr (tm2FromGenerator gen)) (input.map enc)).Dom }
  sorry

end RandomisedGeneration
