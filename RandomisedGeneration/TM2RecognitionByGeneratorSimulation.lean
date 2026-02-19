import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

-- The stack index type for our dovetailing TM2
inductive DovetailStack
  | currentInput  -- the current binary string being tried
  | candidate     -- output accumulated so far for current input
  | target        -- the string we want to recognise
deriving DecidableEq

-- Stack alphabet
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

-- The TM2 transition function built from a generator
def tm2FromGenerator
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    DovetailState Γw Γo Q →
    Turing.TM2.Stmt (dovetailStackAlph Γo) (DovetailState Γw Γo Q) (DovetailSigma Γw Γo Q) :=
  sorry

-- The support set
def tm2FromGeneratorSupport
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    Finset (DovetailState Γw Γo Q) :=
  sorry

-- The support proof
theorem tm2FromGeneratorSupported
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Supports (tm2FromGenerator gen) (tm2FromGeneratorSupport gen) :=
  sorry

def languageRecognisedByTM2 {Λ σ : Type u} {Γ : DovetailStack → Type u}
    [Inhabited (Γ DovetailStack.target)] [FinEnum (Γ DovetailStack.target)]
    [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → Turing.TM2.Stmt Γ Λ σ)
    (S : Finset Λ)
    (_ : Turing.TM2.Supports M S) : Language (Γ DovetailStack.target) :=
  ⟨{ input | default ∉ input ∧ (Turing.TM2.eval M DovetailStack.target input).Dom },
   fun _ hInput => hInput.1⟩

-- Correctness: the TM2 recognises exactly what the generator generates
theorem tm2FromGenerator_correct
    {Γw Γo Q : Type u}
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo]
    (gen : Generator Γw Γo Q)
    (S_gen : Finset Q)
    (hS_gen : GeneratorSupports gen S_gen) :
    languageRecognisedByTM2 (tm2FromGenerator gen)
      (tm2FromGeneratorSupport gen)
      (tm2FromGeneratorSupported gen) =
      generatedLanguage gen S_gen hS_gen :=
  sorry

def languagesRecognisedByTM2s {Γo : Type u} [Inhabited Γo] [FinEnum Γo] : Set (Language Γo) :=
  { L | ∃ (Γw Q : Type u)
          (_ : Fintype Γw)
          (gen : Generator Γw Γo Q)
          (S : Finset (DovetailState Γw Γo Q))
          (_ : Turing.TM2.Supports (tm2FromGenerator gen) S),
        L.val = { input | default ∉ input ∧
          (Turing.TM2.eval (tm2FromGenerator gen) DovetailStack.target input).Dom } }

-- WIP
-- lemma every_tm2_recognisable_language_is_tm1_recognisable {Γo : Type u}
--     [Inhabited Γo] [FinEnum Γo]
--     (L : Language Γo)
--     (hL : L ∈ languagesRecognisedByTM2s (Γo := Γo)) :
--     L ∈ languagesRecognisedByTM1s (Γ := Γo) := by
--   obtain ⟨Γw, Q, hΓw, gen, S, hS, hL_eq⟩ := hL
--   refine ⟨Turing.TM2to1.Γ' DovetailStack (dovetailStackAlph Γo),
--           inferInstance, inferInstance,
--           fun a => (false, fun _ => some a),
--           ?hinj, ?hdef,
--           Turing.TM2to1.Λ' DovetailStack (dovetailStackAlph Γo)
--             (DovetailState Γw Γo Q) (DovetailSigma Γw Γo Q),
--           inferInstance,
--           DovetailSigma Γw Γo Q,
--           inferInstance, inferInstance,
--           Turing.TM2to1.tr (tm2FromGenerator gen),
--           Turing.TM2to1.trSupp (tm2FromGenerator gen) S,
--           Turing.TM2to1.tr_supports (tm2FromGenerator gen) hS,
--           ?hmain⟩
--   case hinj =>
--     intro a b h
--     simp only [Prod.mk.injEq] at h
--     have := h.2
--     have := congr_fun this DovetailStack.target
--     simp at this
--     exact this
--   case hdef =>
--     simp [Turing.TM2to1.Γ']
--     rfl
--   case hmain =>
--     rw [hL_eq]
--     ext input
--     simp only [Set.mem_setOf_eq]
--     constructor
--     · rintro ⟨hnodef, hdom⟩
--       refine ⟨hnodef, ?_⟩
--       rwa [← Turing.TM2to1.tr_eval_dom (tm2FromGenerator gen) DovetailStack.target input]
--     · rintro ⟨hnodef, hdom⟩
--       refine ⟨hnodef, ?_⟩
--       rwa [Turing.TM2to1.tr_eval_dom (tm2FromGenerator gen) DovetailStack.target input]

-- WIP
-- theorem generableLanguages_subset_tm0_recognisable {Γo : Type u}
--     [Inhabited Γo] [FinEnum Γo] :
--     generableLanguages (Γ := Γo) ⊆ languagesRecognisedByTM0s (Γ := Γo) := by
--   intro L hL
--   obtain ⟨Γw, Q, hΓw, gen, S_gen, hS_gen, hgen⟩ := hL
--   have hL_tm2 : L ∈ languagesRecognisedByTM2s (Γo := Γo) :=
--     ⟨Γw, Q, hΓw, gen, tm2FromGeneratorSupport gen, tm2FromGeneratorSupported gen,
--       by sorry
--     ⟩
--   exact every_tm1_recognisable_language_is_tm0_recognisable _
--     (every_tm2_recognisable_language_is_tm1_recognisable _ hL_tm2)

end RandomisedGeneration
