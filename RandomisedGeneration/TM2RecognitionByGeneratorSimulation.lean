/-
══════════════════════════════════════════════════════════════════════════════
  Top-level assembly: every generable language is TM2-recognisable.

  Uses the counter-based abstract machine (`CounterEnumRecognises`) for the
  bisimulation with the TM2.
══════════════════════════════════════════════════════════════════════════════
-/

import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.GreedyGeneration
import RandomisedGeneration.Language
import RandomisedGeneration.GreedyEnum.AbstractMachine
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2Backward
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2Forward

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-!
## Bisimulation: backward direction

If the abstract machine reaches `none` (match found), the TM2 halts.
Each round chains:
  CopyCounterInvariant → InitRunInvariant → (TM2Halts or CopyCounterInvariant next)

Note: `stackTarget` is what sits on the TM2's target stack (= input.reverse).
`cmpTarget` is what counterEnumStep compares cfg.output against (= the actual word).
The TM2's checkOutput compares output.reverse against stackTarget, which is equivalent
to comparing output against cmpTarget when stackTarget = cmpTarget.reverse.
-/

private lemma tm2_halts_of_counterEnum_none
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hInv : CopyCounterInvariant stackTarget counter cfg)
    (n : ℕ)
    (hn : (fun c => c.bind
      (counterEnumStep gen stackTarget.reverse))^[n]
      (some counter) = none) :
    TM2Halts gen cfg := by
  induction n generalizing counter cfg with
  | zero => simp at hn
  | succ n ih =>
    rw [Function.iterate_succ_apply'] at hn
    obtain ⟨cfg₁, hReach₁, hInv₁⟩ :=
      copyCounter_to_initRun gen stackTarget counter cfg hInv
    by_cases h :
        counterEnumStep gen stackTarget.reverse counter
          = none
    · have ⟨hHalt, hOut⟩ :=
        (counterEnumStep_eq_none_iff gen
          stackTarget.reverse counter).mp h
      obtain ⟨cfg_halt, hReach_halt, hHalt_halt⟩ :=
        initRun_match_halts gen hGreedy stackTarget
          counter cfg₁ hInv₁ hHalt
          (by rw [hOut, List.reverse_reverse])
      exact ⟨cfg_halt,
        TM2Reaches_trans hReach₁ hReach_halt,
        hHalt_halt⟩
    · -- counterEnumStep returned some
      have hSome :
          counterEnumStep gen stackTarget.reverse counter
            = some (counterIncrement counter) := by
        simp only [counterEnumStep] at h ⊢
        split <;> simp_all
      have hn' : (fun c => c.bind
          (counterEnumStep gen stackTarget.reverse))^[n]
          (some (counterIncrement counter)) = none := by
        set f := fun c : Option (List (ULift.{u} Bool)) =>
          c.bind
            (counterEnumStep gen stackTarget.reverse)
        have hf : f (some counter) =
            some (counterIncrement counter) := by
          simp [f, hSome]
        change f^[n] (some (counterIncrement counter))
          = none
        rw [← hf,
          show f^[n] (f (some counter)) =
            f (f^[n] (some counter)) from
          (Function.Semiconj.iterate_right
            (fun x => rfl) n (some counter)).symm]
        exact hn
      obtain ⟨cfg₂, hReach₂, hInv₂⟩ :=
        initRun_no_match_to_copyCounter gen hGreedy
          stackTarget counter
          cfg₁ hInv₁ h
      obtain ⟨cfg₃, hReach₃, hHalt₃⟩ :=
        ih (counterIncrement counter) cfg₂ hInv₂ hn'
      exact ⟨cfg₃,
        TM2Reaches_trans
          (TM2Reaches_trans hReach₁ hReach₂) hReach₃,
        hHalt₃⟩

theorem greedyEnumTM2_halts_iff_CounterEnumRecognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy) (target : List Γo) :
    (GreedyEnum.GEEval gen target.reverse).Dom ↔
    GreedyEnum.CounterEnumRecognises gen target := by
  rw [GreedyEnum.eval_dom_iff_TM2Halts]
  constructor
  · exact tm2_halts_implies_counterEnumRecognises gen hGreedy target
  · intro ⟨n, hn⟩
    have hInit :=
      init_copyCounterInvariant gen target.reverse
    exact tm2_halts_of_counterEnum_none gen hGreedy
      target.reverse [] _ hInit n
      (by rwa [List.reverse_reverse])

theorem greedyEnumMachine_recognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) (hGreedy : gen.IsGreedy) (target : List Γo) :
    (GreedyEnum.GEEval gen target.reverse).Dom ↔
    target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
  rw [greedyEnumTM2_halts_iff_CounterEnumRecognises gen hGreedy]
  rw [GreedyEnum.CounterEnumRecognises_iff_Computes gen hGreedy]
  simp only [generatedLanguage, Set.mem_setOf_eq]

end GreedyEnum

lemma every_generable_language_is_tm2_recognisable
    {Γ : Type u} [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ) (hL : L ∈ generableLanguages) :
    L ∈ languagesRecognisedByTM2s := by
  obtain ⟨Γw, Q, hΓwfinenum, hQdec, gen, S_gen, hS_gen, hgen⟩ := hL
  haveI : DecidableEq Q := hQdec
  let ggen := gen.greedify
  let S_ggen := S_gen ×ˢ (Finset.univ : Finset (Option Bool))
  have hS_ggen : GeneratorSupports ggen S_ggen := GeneratorSupports_greedify gen S_gen hS_gen
  have hGreedy : ggen.IsGreedy := gen.greedify_isGreedy
  have hLang := generatedLanguage_greedify gen S_gen hS_gen
  let gen' := ggen.restrictToSupport S_ggen hS_ggen
  haveI : Fintype ↥S_ggen := inferInstance
  haveI : DecidableEq ↥S_ggen := inferInstance
  haveI : FinEnum ↥S_ggen := FinEnum.ofList (Finset.univ.val.toList) (by simp)
  haveI : Inhabited ↥S_ggen := ⟨gen'.init⟩
  haveI : Inhabited Γw := ⟨gen.blank⟩
  haveI : ∀ k, Inhabited (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  haveI : ∀ k, Fintype (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  haveI : ∀ k, DecidableEq (GreedyEnum.stackAlphabet Γw Γ ↥S_ggen k) :=
    fun k => by cases k <;> simp only [GreedyEnum.stackAlphabet] <;> infer_instance
  have hGreedy' : gen'.IsGreedy :=
    Generator.restrictToSupport_isGreedy ggen S_ggen hS_ggen hGreedy
  refine ⟨
    GreedyEnum.GreedyEnumStack,
    inferInstance, inferInstance, inferInstance,
    GreedyEnum.stackAlphabet Γw Γ ↥S_ggen,
    inferInstance, inferInstance, inferInstance, rfl,
    GreedyEnum.GreedyEnumLabel,
    inferInstance, inferInstance,
    GreedyEnum.GreedyEnumSigma Γw Γ ↥S_ggen,
    inferInstance, inferInstance,
    GreedyEnum.greedyEnumMachine gen',
    Finset.univ,
    ⟨Finset.mem_univ _, fun q _ => by
      cases q <;> simp only [GreedyEnum.greedyEnumMachine,
              GreedyEnum.copyCounter, GreedyEnum.copyCounter_restore, GreedyEnum.initRun,
              GreedyEnum.runStep, GreedyEnum.runStep_apply, GreedyEnum.runStep_moveHead,
              GreedyEnum.checkOutput, GreedyEnum.checkOutput_restoreTarget,
              GreedyEnum.clearInput, GreedyEnum.clearWorkL, GreedyEnum.clearWorkR,
              GreedyEnum.clearOutput, GreedyEnum.counter_increment,
              GreedyEnum.counter_increment_loop, GreedyEnum.counter_increment_restore,
              Turing.TM2.SupportsStmt] <;>
            simp (config := { decide := true })
      ⟩,
    ?_⟩
  subst hgen
  ext input
  simp only [Set.mem_setOf_eq]
  have lang_eq : generatedLanguage gen S_gen hS_gen =
      generatedLanguage gen' Finset.univ (generator_supports_univ gen') := by
    rw [hLang]; ext w; simp only [generatedLanguage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨input, h⟩; exact ⟨input, restrictToSupport_Computes ggen S_ggen hS_ggen h⟩
    · rintro ⟨input, h⟩; exact ⟨input, restrictToSupport_Computes_lift ggen S_ggen hS_ggen h⟩
  rw [lang_eq]
  exact (GreedyEnum.greedyEnumMachine_recognises gen' hGreedy' input).symm

end RandomisedGeneration
