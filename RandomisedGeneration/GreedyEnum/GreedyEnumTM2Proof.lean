import Mathlib
import RandomisedGeneration.GreedyEnum.AbstractMachine
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2

namespace RandomisedGeneration

universe u

namespace GreedyEnum

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]
set_option linter.unusedSectionVars false

abbrev GECfg (Γw Γo Q : Type u) [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :=
  Turing.TM2.Cfg.{u,u,u,u}
    (stackAlphabet Γw Γo Q)
    GreedyEnumLabel.{u}
    (GreedyEnumSigma Γw Γo Q)

abbrev GEStep (gen : Generator Γw Γo Q) : GECfg Γw Γo Q → Option (GECfg Γw Γo Q) :=
  Turing.TM2.step (greedyEnumMachine gen)

abbrev GEEval (gen : Generator Γw Γo Q) (target : List Γo) : Part (List Γo) :=
  @Turing.TM2.eval.{u,u,u,u} GreedyEnumStack (stackAlphabet Γw Γo Q)
    GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) _ _ _
    (greedyEnumMachine gen) GreedyEnumStack.target target

def TM2Reaches (gen : Generator Γw Γo Q) (cfg cfg' : GECfg Γw Γo Q) : Prop :=
  Relation.ReflTransGen (fun a b => GEStep gen a = some b) cfg cfg'

def TM2Halts (gen : Generator Γw Γo Q) (cfg : GECfg Γw Γo Q) : Prop :=
  ∃ cfg', TM2Reaches gen cfg cfg' ∧ GEStep gen cfg' = none

lemma TM2Reaches_trans {gen : Generator Γw Γo Q}
    {cfg₁ cfg₂ cfg₃ : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
      GreedyEnumLabel (GreedyEnumSigma Γw Γo Q)}
    (h₁ : TM2Reaches gen cfg₁ cfg₂) (h₂ : TM2Reaches gen cfg₂ cfg₃) :
    TM2Reaches gen cfg₁ cfg₃ :=
  Relation.ReflTransGen.trans h₁ h₂

def WorkTapeMatches
    (gen : Generator Γw Γo Q)
    (work : ℤ → Γw)
    (workIndex : ℤ)
    (workL workR : List Γw) : Prop :=
  (∀ i : ℕ, (h : i < workR.length) →
    workR.get ⟨i, h⟩ = work (workIndex + i)) ∧
  (∀ i : ℕ, i ≥ workR.length →
    work (workIndex + i) = gen.blank) ∧
  (∀ i : ℕ, (h : i < workL.length) →
    workL.get ⟨i, h⟩ = work (workIndex - (↑i + 1))) ∧
  (∀ i : ℕ, i ≥ workL.length →
    work (workIndex - (↑i + 1)) = gen.blank)

structure CopyCounterInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []

structure CopyCounterRestoreInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = counter.reverse
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

structure InitRunInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.initRun
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

structure RunStepInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop gcfg.inputIndex
  h_transQ      : cfg.var.transQ = some gcfg.state
  h_work        : WorkTapeMatches gen gcfg.work gcfg.workIndex
                    (cfg.stk GreedyEnumStack.workL) (cfg.stk GreedyEnumStack.workR)
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg.output.reverse

structure RunStepApplyInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (q' : Q) (w' : Γw) (o : Option Γo) (wd : WorkTapeDirection)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep_apply
  h_delta       : gen.δ gcfg.state
                    (gcfg.input gcfg.inputIndex)
                    (gcfg.work gcfg.workIndex)
                  = some (q', w', o, InputTapeDirection.R, wd)
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop (gcfg.inputIndex + 1)
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg.output.reverse
  h_workL       : ∀ i : ℕ, (h : i < (cfg.stk GreedyEnumStack.workL).length) →
                    (cfg.stk GreedyEnumStack.workL).get ⟨i, h⟩ =
                      gcfg.work (gcfg.workIndex - (↑i + 1))
  h_workL_blank : ∀ i : ℕ, i ≥ (cfg.stk GreedyEnumStack.workL).length →
                    gcfg.work (gcfg.workIndex - (↑i + 1)) = gen.blank
  h_workR       : ∀ i : ℕ, (h : i < (cfg.stk GreedyEnumStack.workR).length) →
                    (cfg.stk GreedyEnumStack.workR).get ⟨i, h⟩ =
                      gcfg.work (gcfg.workIndex + (↑i + 1))
  h_workR_blank : ∀ i : ℕ, i ≥ (cfg.stk GreedyEnumStack.workR).length →
                    gcfg.work (gcfg.workIndex + (↑i + 1)) = gen.blank
  h_transQ      : cfg.var.transQ      = some q'
  h_transW      : cfg.var.transW      = w'
  h_transOut    : cfg.var.transOut     = o
  h_transWDir   : cfg.var.transWDir   = wd
  h_transHalted : cfg.var.transHalted = false

structure RunStepMoveHeadInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg gcfg' : GenConfig Γw Γo Q)
    (wd : WorkTapeDirection)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.runStep_moveHead
  h_gen_step    : step gen gcfg = some gcfg'
  h_wd          : gcfg'.workIndex = gcfg.workIndex + (wd : ℤ)
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_input       : cfg.stk GreedyEnumStack.input       = counter.drop gcfg'.inputIndex
  h_output      : cfg.stk GreedyEnumStack.output      = gcfg'.output.reverse
  h_work        : WorkTapeMatches gen gcfg'.work gcfg.workIndex
                    (cfg.stk GreedyEnumStack.workL) (cfg.stk GreedyEnumStack.workR)
  h_transWDir   : cfg.var.transWDir = wd

/-- When input is exhausted and the generator halts, runStep branches
    to checkOutput. -/
structure CheckOutputInvariant
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (remaining_target : List Γo)
    (remaining_output : List Γo)
    (cfg : GECfg Γw Γo Q)
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.checkOutput
  h_target      : cfg.stk GreedyEnumStack.target = remaining_target
  h_output      : cfg.stk GreedyEnumStack.output = remaining_output
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget =
      (stackTarget.take
        (stackTarget.length - remaining_target.length)).reverse
  h_counter     : cfg.stk GreedyEnumStack.counter = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_input       : cfg.stk GreedyEnumStack.input = []
  h_suffix      : stackTarget.drop
      (stackTarget.length - remaining_target.length)
      = remaining_target

structure ClearInputInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.clearInput
  h_target      : cfg.stk GreedyEnumStack.target = target
  h_counter     : cfg.stk GreedyEnumStack.counter = counter
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget = []

structure CounterIncrementInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = counter
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []

section CopyCounterPhase

private structure CopyCounterLoopInvariant
    (target : List Γo)
    (remaining : List (ULift.{u} Bool))
    (saved : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = remaining
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = saved
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private structure CopyCounterRestoreLoopInvariant
    (target : List Γo)
    (restored : List (ULift.{u} Bool))
    (remaining : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.copyCounter_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = restored
  h_input       : cfg.stk GreedyEnumStack.input       = restored
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = remaining
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private lemma copyCounter_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (remaining saved : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterLoopInvariant target remaining saved cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterRestoreLoopInvariant target [] (remaining.reverse ++ saved) cfg' := by
  induction remaining generalizing saved cfg with
  | nil =>
    simp only [List.reverse_nil, List.nil_append]
    refine ⟨⟨some GreedyEnumLabel.copyCounter_restore,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hc : S GreedyEnumStack.counter = [] := hinv.h_counter
        simp only [Turing.TM2.step, greedyEnumMachine,
                   copyCounter, Turing.TM2.stepAux, hc, List.head?,
                   Option.map, Option.isNone, cond_true]
    · exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
             hinv.h_saveCounter, hinv.h_workL, hinv.h_workR,
             hinv.h_output, hinv.h_saveTarget⟩
  | cons b rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        CopyCounterLoopInvariant target rest (b :: saved) cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.copyCounter,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.counter => rest
                 | GreedyEnumStack.saveCounter => b :: saved
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hc : S GreedyEnumStack.counter = b :: rest := hinv.h_counter
          have hsc : S GreedyEnumStack.saveCounter = saved := hinv.h_saveCounter
          simp only [Turing.TM2.step, greedyEnumMachine,
                     copyCounter, Turing.TM2.stepAux, hc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons, Option.getD_some,
              ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hsc]
      · exact ⟨rfl, hinv.h_target, rfl, rfl, hinv.h_input,
               hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₁, hr₁, hinv₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, hinv₂⟩ := ih (b :: saved) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
    convert hinv₂ using 1
    simp [List.reverse_cons, List.append_assoc]

private lemma copyCounter_restore_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (restored remaining : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterRestoreLoopInvariant target restored remaining cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      InitRunInvariant target (remaining.reverse ++ restored) cfg' := by
  induction remaining generalizing restored cfg with
  | nil =>
    simp only [List.reverse_nil, List.nil_append]
    refine ⟨⟨some GreedyEnumLabel.initRun,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        have hl := hinv.h_label; simp only at hl; subst hl
        have hsc : S GreedyEnumStack.saveCounter = [] := hinv.h_saveCounter
        simp only [Turing.TM2.step, greedyEnumMachine,
                   copyCounter_restore, Turing.TM2.stepAux, hsc,
                   List.head?, Option.map, Option.isNone, cond_true]
    · exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
             hinv.h_saveCounter, hinv.h_workL, hinv.h_workR,
             hinv.h_output, hinv.h_saveTarget⟩
  | cons b rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        CopyCounterRestoreLoopInvariant target (b :: restored) rest cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.copyCounter_restore,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.counter => b :: restored
                 | GreedyEnumStack.input => b :: restored
                 | GreedyEnumStack.saveCounter => rest
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hsc : S GreedyEnumStack.saveCounter = b :: rest := hinv.h_saveCounter
          have hc : S GreedyEnumStack.counter = restored := hinv.h_counter
          have hi : S GreedyEnumStack.input = restored := hinv.h_input
          simp only [Turing.TM2.step, greedyEnumMachine,
                     copyCounter_restore, Turing.TM2.stepAux, hsc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons, Option.getD_some,
              ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hc, hi]
      · exact ⟨rfl, hinv.h_target, rfl, rfl, rfl,
               hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₁, hr₁, hinv₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, hinv₂⟩ := ih (b :: restored) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
    convert hinv₂ using 1
    simp [List.reverse_cons, List.append_assoc]

end CopyCounterPhase

section RunPhase

/-- After initRun loads the generator state, we're at runStep with
    the initial GenConfig. -/
private lemma initRun_to_runStep
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
      GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : InitRunInvariant stackTarget counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter
        (initConfig gen (counterToInput counter)) cfg' := by
  refine ⟨⟨some GreedyEnumLabel.runStep,
           { cfg.var with
             transQ := some gen.init
             transW := gen.blank },
           cfg.stk⟩, ?_, ?_⟩
  · apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at *
      have hl := hinv.h_label; simp only at hl; subst hl
      simp only [GEStep, Turing.TM2.step,
                 greedyEnumMachine, initRun,
                 Turing.TM2.stepAux]
  · constructor
    · -- h_label
      rfl
    · -- h_target
      exact hinv.h_target
    · -- h_counter
      exact hinv.h_counter
    · -- h_saveCounter
      exact hinv.h_saveCounter
    · -- h_saveTarget
      exact hinv.h_saveTarget
    · -- h_input
      rw [hinv.h_input]; simp [initConfig]
    · -- h_transQ
      rfl
    · -- h_work: WorkTapeMatches
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i h; rw [hinv.h_workR] at h; simp at h
      · intro i _; simp [initConfig]
      · intro i h; rw [hinv.h_workL] at h; simp at h
      · intro i _; simp [initConfig]
    · -- h_output
      rw [hinv.h_output]; simp [initConfig]

/-- One iteration of the run loop: if input is non-empty and delta doesn't halt,
    we advance the GenConfig by one step and return to runStep. -/
private lemma runStep_step
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg gcfg' : GenConfig Γw Γo Q)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hInput : gcfg.inputIndex < counter.length)
    (hStep : step gen gcfg = some gcfg') :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter gcfg' cfg' := by
  sorry
  -- This is the big one. Path: runStep → runStep_apply → runStep_moveHead → runStep.
  -- Needs to go through the branch on input non-empty, pop input, peek workR,
  -- apply delta (non-halting), push new workR, emit output, move head.
  -- You may want to split this into sub-lemmas:
  --   runStep_to_apply, runStep_apply_to_moveHead, runStep_moveHead_to_runStep

/-- Run the full loop for N steps, chaining runStep_step. -/
private lemma runStep_loop
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (n : ℕ)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hSteps : ∀ i, i < n → gcfg.inputIndex + i < counter.length)
    (hAlive : ∀ i, i < n → ¬IsHalting gen (stepNHalt gen gcfg i)) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      RunStepInvariant gen stackTarget counter (stepNHalt gen gcfg n) cfg' := by
  sorry
  -- Induction on n, using runStep_step at each iteration.

end RunPhase


section CheckOutputPhase

/-- When the run loop ends (input exhausted), we reach checkOutput
    or clearInput depending on whether the generator halted.
    This handles the halting case. -/
private lemma runStep_exhausted_halted_to_checkOutput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : GECfg Γw Γo Q)
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hExhausted : gcfg.inputIndex = counter.length)
    (hHalted : IsHalting gen gcfg)
    (hInput : gcfg.input = counterToInput counter) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget counter
        stackTarget gcfg.output.reverse cfg' := by
  have hInputEmpty : cfg.stk GreedyEnumStack.input = [] := by
    rw [hinv.h_input, hExhausted, List.drop_length]
  have hDelta : gen.δ gcfg.state
      (gcfg.input gcfg.inputIndex)
      (gcfg.work gcfg.workIndex) = none := by
    have h := hHalted
    simp only [IsHalting, step] at h
    revert h
    cases gen.δ gcfg.state
      (gcfg.input gcfg.inputIndex)
      (gcfg.work gcfg.workIndex) with
    | none => intro; rfl
    | some val =>
      obtain ⟨q', w', out?, inDir, workDir⟩ := val
      simp
  have hInputBit :
      gcfg.input gcfg.inputIndex = false := by
    rw [hInput, hExhausted]; simp [counterToInput]
  -- The TM2 traces through modified runStep:
  -- peek input (empty) → inputBit=false →
  -- peek workR → [pop if non-empty] →
  -- applyDelta → transHalted=true → goto checkOutput
  --
  -- applyDelta with gen.δ = none sets transHalted := true
  cases hWR : cfg.stk GreedyEnumStack.workR with
  | nil =>
    have hBlank : gcfg.work gcfg.workIndex = gen.blank := by
      have := hinv.h_work.2.1 0 (by simp [hWR])
      simp only [CharP.cast_eq_zero, add_zero] at this
      exact this
    -- One TM2 step to checkOutput, stacks unchanged
    refine ⟨⟨some GreedyEnumLabel.checkOutput,
             applyDelta gen
               { transQ := cfg.var.transQ
                 transW := gen.blank
                 transWDir := cfg.var.transWDir
                 transOut := cfg.var.transOut
                 transHalted := cfg.var.transHalted
                 inputBit := false
                 carry := cfg.var.carry
                 peekBit := some false
                 peekTarget := cfg.var.peekTarget
                 peekOut := cfg.var.peekOut },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hQ := hinv.h_transQ; simp only at hQ
        rw [hInputBit, hBlank] at hDelta
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine, runStep,
                   Turing.TM2.stepAux,
                   hInputEmpty, hWR, List.head?,
                   Option.isSome, Option.getD, BEq.beq,
                   applyDelta, hQ,
                   hDelta]
        have h1 : Option.instBEq.beq
            (some false) (some false) = true := by decide
        have h2 : Option.instBEq.beq
            (some false) (some true) = false := by decide
        rw [h1, h2, cond_true, cond_false]
        -- applyDelta with none → transHalted = true → checkOutput
        simp only [cond_true]
    · constructor
      · -- h_label
        rfl
      · -- h_target
        exact hinv.h_target
      · -- h_output
        rw [hinv.h_output]
      · -- h_saveTarget
        simp [hinv.h_saveTarget]
      · -- h_counter
        exact hinv.h_counter
      · -- h_saveCounter
        exact hinv.h_saveCounter
      · -- h_input
        exact hInputEmpty
      · -- h_suffix
        simp
  | cons w rest =>
    have hHead : w = gcfg.work gcfg.workIndex := by
      have := hinv.h_work.1 0 (by simp [hWR])
      simp only [List.get_eq_getElem, hWR, List.getElem_cons_zero,
        CharP.cast_eq_zero, add_zero] at this
      exact this
    -- One TM2 step, workR gets popped
    refine ⟨⟨some GreedyEnumLabel.checkOutput,
             applyDelta gen
               { transQ := cfg.var.transQ
                 transW := w
                 transWDir := cfg.var.transWDir
                 transOut := cfg.var.transOut
                 transHalted := cfg.var.transHalted
                 inputBit := false
                 carry := cfg.var.carry
                 peekBit := some true
                 peekTarget := cfg.var.peekTarget
                 peekOut := cfg.var.peekOut },
             fun k => match k with
               | GreedyEnumStack.workR => rest
               | other => cfg.stk other⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hQ := hinv.h_transQ; simp only at hQ
        rw [hInputBit] at hDelta
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine, runStep,
                   Turing.TM2.stepAux,
                   hInputEmpty, hWR, List.head?,
                   Option.isSome, Option.getD, BEq.beq,
                   List.tail_cons,
                   applyDelta, hQ]
        have h1 : Option.instBEq.beq
            (some false) (some false) = true := by decide
        have h2 : Option.instBEq.beq
            (some true) (some true) = true := by decide
        rw [h1, h2, cond_true, cond_true]
        rw [hHead, hDelta]
        simp only [cond_true]
        congr 1; congr 1
        funext k; cases k <;> simp [Function.update]
    · constructor
      · -- h_label
        rfl
      · -- h_target
        exact hinv.h_target
      · -- h_output
        rw [hinv.h_output]
      · -- h_saveTarget
        simp [hinv.h_saveTarget]
      · -- h_counter
        exact hinv.h_counter
      · -- h_saveCounter
        exact hinv.h_saveCounter
      · -- h_input
        exact hInputEmpty
      · -- h_suffix
        simp

/-- When the run loop ends because delta halted (not input exhausted),
    we reach checkOutput. -/
private lemma runStep_halted_to_checkOutput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : GECfg Γw Γo Q)
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hInput : gcfg.inputIndex < counter.length)
    (hHalted : gen.δ gcfg.state (gcfg.input gcfg.inputIndex) (gcfg.work gcfg.workIndex) = none) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget counter
        stackTarget gcfg.output.reverse cfg' := by
  sorry
  -- runStep peeks input (non-empty), pops, peeks workR, applies delta,
  -- delta returns none → transHalted = true → goto checkOutput.

private lemma take_succ_reverse_cons
    {α : Type*} (l : List α) (n : ℕ) (h : n < l.length) :
    (l.take (n + 1)).reverse = l[n] :: (l.take n).reverse := by
  rw [List.take_add_one, List.reverse_append]
  simp [List.getElem?_eq_getElem h]

private lemma checkOutput_step_match
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (t : Γo) (rest_t rest_o : List Γo)
    (cfg : GECfg Γw Γo Q)
    (hinv : CheckOutputInvariant stackTarget counter
        (t :: rest_t) (t :: rest_o) cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CheckOutputInvariant stackTarget counter
        rest_t rest_o cfg' := by
  have hSuffix := hinv.h_suffix
  have hLen : (t :: rest_t).length ≤ stackTarget.length := by
    have := congr_arg List.length hSuffix
    simp [List.length_drop] at this
    simp only [List.length_cons]
    omega
  have hIdx : stackTarget.length - (t :: rest_t).length < stackTarget.length := by
    have : (t :: rest_t).length ≥ 1 := by simp [List.length_cons]
    omega
  have hAt : stackTarget[stackTarget.length -
      (t :: rest_t).length] = t := by
    have h : stackTarget[stackTarget.length - (t :: rest_t).length]? = some t := by
      rw [← List.head?_drop, hSuffix]; rfl
    simp only [List.length_cons] at h
    have hEq : stackTarget.length - (t :: rest_t).length =
        stackTarget.length - (rest_t.length + 1) := by
      simp [List.length_cons]
    simp only [List.length_cons] at hIdx ⊢
    have := List.getElem?_eq_getElem hIdx
    rw [this] at h
    exact Option.some.inj h
  -- TM2 steps: peek target (some t), peek output (some t),
  -- not both none, not one none, compare equal,
  -- pop both, push target to saveTarget, goto checkOutput
  refine ⟨⟨some GreedyEnumLabel.checkOutput,
           { cfg.var with
             peekTarget := some t
             peekOut := some t },
           fun k => match k with
             | GreedyEnumStack.target => rest_t
             | GreedyEnumStack.output => rest_o
             | GreedyEnumStack.saveTarget =>
                 t :: (stackTarget.take
                   (stackTarget.length -
                     (t :: rest_t).length)).reverse
             | other => cfg.stk other⟩, ?_, ?_⟩
  · apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at *
      have hl := hinv.h_label; simp only at hl; subst hl
      have ht := hinv.h_target; simp only at ht
      have ho := hinv.h_output; simp only at ho
      have hst := hinv.h_saveTarget; simp only at hst
      simp only [GEStep, Turing.TM2.step,
                 greedyEnumMachine, checkOutput,
                 Turing.TM2.stepAux,
                 ht, ho, List.head?,
                 Option.isNone, Bool.and_false,
                 cond_false, Bool.or_false,
                 decide_true, cond_true,
                 List.tail_cons, Option.getD_some]
      simp only [Option.some.injEq,
                 Turing.TM2.Cfg.mk.injEq, true_and]
      ext k; cases k <;>
        simp only [Function.update, reduceCtorEq,
                   ↓reduceDIte, List.getElem?_tail,
                   hst, List.length_cons]
      rw [ho, List.getElem?_cons_succ]
  · refine ⟨rfl, rfl, rfl, ?_,
            hinv.h_counter, hinv.h_saveCounter,
            hinv.h_input, ?_⟩
    · -- h_saveTarget
      rw [show stackTarget.length - rest_t.length =
          (stackTarget.length -
            (t :: rest_t).length) + 1
          from by
            simp [List.length_cons]
            have : (t :: rest_t).length = rest_t.length + 1 := by simp [List.length_cons]
            omega
          ]
      simp only []
      rw [take_succ_reverse_cons stackTarget (stackTarget.length - (t :: rest_t).length) hIdx, hAt]
    · -- h_suffix: stackTarget.drop (...) = rest_t
      have hEq : stackTarget.length - rest_t.length =
        (stackTarget.length - (t :: rest_t).length) + 1 := by
        have : (t :: rest_t).length = rest_t.length + 1 := by
          simp [List.length_cons]
        omega
      rw [hEq]
      have : List.drop ((stackTarget.length - (t :: rest_t).length) + 1) stackTarget =
        List.drop 1 (List.drop (stackTarget.length - (t :: rest_t).length) stackTarget) := by
        rw [List.drop_drop]
      rw [this, hSuffix, show List.drop 1 (t :: rest_t) = rest_t from rfl]

/-- checkOutput with both stacks empty → halt. -/
private lemma checkOutput_both_empty_halts
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hinv : CheckOutputInvariant stackTarget counter
        [] [] cfg) :
    TM2Halts gen cfg := by
  -- One TM2 step: peek target (none), peek output (none),
  -- both none → halt
  refine ⟨⟨none,
           { cfg.var with
             peekTarget := none
             peekOut := none },
           cfg.stk⟩, ?_, ?_⟩
  · apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at *
      have hl := hinv.h_label; simp only at hl; subst hl
      have ht := hinv.h_target; simp only at ht
      have ho := hinv.h_output; simp only at ho
      simp only [GEStep, Turing.TM2.step,
                 greedyEnumMachine, checkOutput,
                 Turing.TM2.stepAux,
                 ht, ho, List.head?,
                 Option.isNone, Bool.and_self,
                 cond_true]
  · -- GEStep on halted config = none
    simp [GEStep, Turing.TM2.step]

/-- Chain checkOutput over matching lists. -/
private lemma checkOutput_matching_lists_halt
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (matched : List Γo)
    (cfg : GECfg Γw Γo Q)
    (hinv : CheckOutputInvariant stackTarget counter
        matched matched cfg) :
    TM2Halts gen cfg := by
  induction matched generalizing cfg with
  | nil =>
    exact checkOutput_both_empty_halts gen stackTarget
      counter cfg hinv
  | cons t rest ih =>
    obtain ⟨cfg', hr, hinv'⟩ :=
      checkOutput_step_match gen stackTarget counter
        t rest rest cfg hinv
    obtain ⟨cfg'', hr', hhalted⟩ := ih cfg' hinv'
    exact ⟨cfg'', TM2Reaches_trans hr hr', hhalted⟩

/-- Restore target from saveTarget, then goto clearInput. -/
private lemma checkOutput_restore_to_clearInput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (remaining_target : List Γo)
    (saved : List Γo)
    (cfg : GECfg Γw Γo Q)
    (h_label : cfg.l = some GreedyEnumLabel.checkOutput_restoreTarget)
    (h_target : cfg.stk GreedyEnumStack.target = remaining_target)
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = saved)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = [])
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_concat : saved.reverse ++ remaining_target = stackTarget) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      ClearInputInvariant stackTarget counter cfg' := by
  induction saved generalizing remaining_target cfg with
  | nil =>
    -- saveTarget empty: one step, goto clearInput
    simp only [List.reverse_nil, List.nil_append] at h_concat
    refine ⟨⟨some GreedyEnumLabel.clearInput,
             { cfg.var with peekTarget := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *; subst h_label
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine,
                   checkOutput_restoreTarget,
                   Turing.TM2.stepAux,
                   h_saveTarget, List.head?,
                   Option.isNone, cond_true]
    · exact ⟨rfl, by rw [← h_concat]; exact h_target,
           h_counter, h_saveCounter, h_saveTarget⟩
  | cons s rest ih =>
    -- Pop s from saveTarget, push to target, loop
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.checkOutput_restoreTarget ∧
        cfg₁.stk GreedyEnumStack.target = s :: remaining_target ∧
        cfg₁.stk GreedyEnumStack.saveTarget = rest ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] ∧
        cfg₁.stk GreedyEnumStack.input = [] := by
      refine ⟨⟨some GreedyEnumLabel.checkOutput_restoreTarget,
               { cfg.var with peekTarget := some s },
               fun k => match k with
                 | GreedyEnumStack.target => s :: remaining_target
                 | GreedyEnumStack.saveTarget => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, rfl, h_counter,
              h_saveCounter, h_input⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *; subst h_label
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine,
                   checkOutput_restoreTarget,
                   Turing.TM2.stepAux,
                   h_saveTarget, List.head?,
                   Option.isNone, cond_false,
                   List.tail_cons, Option.getD_some]
        simp only [Option.some.injEq,
                   Turing.TM2.Cfg.mk.injEq, true_and]
        ext k; cases k <;>
          simp [Function.update, h_target]
    obtain ⟨cfg₁, hr₁, hl₁, ht₁, hst₁, hc₁,
            hsc₁, hi₁⟩ := hstep
    have hConcat : rest.reverse ++ (s :: remaining_target)
        = stackTarget := by
      simp [List.reverse_cons, List.append_assoc] at h_concat
      simpa [List.reverse_cons, List.append_assoc,
             List.singleton_append] using h_concat
    obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
      ih (s :: remaining_target) cfg₁ hl₁ ht₁ hst₁
        hc₁ hsc₁ hi₁ hConcat
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, hinv₂⟩

private lemma checkOutput_mismatch_to_clearInput
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (remaining_target remaining_output : List Γo)
    (cfg : GECfg Γw Γo Q)
    (hinv : CheckOutputInvariant stackTarget counter
        remaining_target remaining_output cfg)
    (hMismatch : remaining_target ≠ remaining_output) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      ClearInputInvariant stackTarget counter cfg' := by
  induction remaining_target generalizing remaining_output cfg with
  | nil =>
    -- remaining_target = [], remaining_output ≠ [] (from hMismatch)
    -- checkOutput: peek target (none), peek output (some _),
    -- not both none, one is none → goto checkOutput_restoreTarget
    cases remaining_output with
    | nil => exact absurd rfl hMismatch
    | cons o rest_o =>
      have hstep : ∃ cfgR : GECfg Γw Γo Q,
          TM2Reaches gen cfg cfgR ∧
          cfgR.l = some GreedyEnumLabel.checkOutput_restoreTarget ∧
          cfgR.stk GreedyEnumStack.target = [] ∧
          cfgR.stk GreedyEnumStack.saveTarget =
            cfg.stk GreedyEnumStack.saveTarget ∧
          cfgR.stk GreedyEnumStack.counter = counter ∧
          cfgR.stk GreedyEnumStack.saveCounter = [] ∧
          cfgR.stk GreedyEnumStack.input = [] := by
        refine ⟨⟨some GreedyEnumLabel.checkOutput_restoreTarget,
                 { cfg.var with
                   peekTarget := none
                   peekOut := some o },
                 cfg.stk⟩, ?_, rfl, hinv.h_target,
               rfl, hinv.h_counter, hinv.h_saveCounter,
               hinv.h_input⟩
        apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          simp only at *
          have hl := hinv.h_label; simp only at hl; subst hl
          have ht := hinv.h_target; simp only at ht
          have ho := hinv.h_output; simp only at ho
          simp only [GEStep, Turing.TM2.step,
                     greedyEnumMachine, checkOutput,
                     Turing.TM2.stepAux,
                     ht, ho, List.head?,
                     Option.isNone, Bool.true_and,
                     cond_false, Bool.true_or,
                     cond_true]
      obtain ⟨cfgR, hrR, hlR, htR, hstR, hcR, hscR, hiR⟩ := hstep
      -- The saved target on cfgR equals what was on cfg
      -- hinv.h_saveTarget tells us about cfg's saveTarget
      -- hinv.h_suffix with remaining = [] gives stackTarget.drop (stackTarget.length) = []
      -- and hinv.h_saveTarget says cfg.stk saveTarget =
      -- (stackTarget.take stackTarget.length).reverse = stackTarget.reverse
      -- so cfgR.stk saveTarget = stackTarget.reverse
      have hSaved : cfgR.stk GreedyEnumStack.saveTarget =
          stackTarget.reverse := by
        rw [hstR, hinv.h_saveTarget]
        simp
      have hConcat : stackTarget.reverse.reverse
          ++ ([] : List Γo) = stackTarget := by
        simp [List.reverse_reverse]
      obtain ⟨cfg', hr', hinv'⟩ :=
        checkOutput_restore_to_clearInput gen
          stackTarget counter ([] : List Γo)
          stackTarget.reverse cfgR
          hlR htR hSaved hcR hscR hiR
          hConcat
      exact ⟨cfg', TM2Reaches_trans hrR hr', hinv'⟩
  | cons t rest_t ih =>
    cases remaining_output with
    | nil =>
      -- remaining_target = t :: rest_t, remaining_output = []
      -- checkOutput: peek target (some t), peek output (none),
      -- one is none → goto checkOutput_restoreTarget
      obtain ⟨cfgR, hrR, hlR, htR, hstR, hcR,
              hscR, hiR, hoR⟩ :
          ∃ cfgR : GECfg Γw Γo Q,
            TM2Reaches gen cfg cfgR ∧
            cfgR.l = some GreedyEnumLabel.checkOutput_restoreTarget ∧
            cfgR.stk GreedyEnumStack.target = t :: rest_t ∧
            cfgR.stk GreedyEnumStack.saveTarget =
              (stackTarget.take
                (stackTarget.length -
                  (t :: rest_t).length)).reverse ∧
            cfgR.stk GreedyEnumStack.counter = counter ∧
            cfgR.stk GreedyEnumStack.saveCounter = [] ∧
            cfgR.stk GreedyEnumStack.input = [] ∧
            cfgR.stk GreedyEnumStack.output = [] := by
        refine ⟨⟨some GreedyEnumLabel.checkOutput_restoreTarget,
               { cfg.var with
                 peekTarget := some t
                 peekOut := none },
               cfg.stk⟩, ?_, rfl, hinv.h_target,
             hinv.h_saveTarget, hinv.h_counter,
             hinv.h_saveCounter, hinv.h_input,
             hinv.h_output⟩
        apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          simp only at *
          have hl := hinv.h_label; simp only at hl; subst hl
          have ht := hinv.h_target; simp only at ht
          have ho := hinv.h_output; simp only at ho
          simp only [GEStep, Turing.TM2.step,
                    greedyEnumMachine, checkOutput,
                    Turing.TM2.stepAux,
                    ht, ho, List.head?,
                    Option.isNone, Bool.and_true,
                    cond_false, Bool.or_true,
                    cond_true]
      obtain ⟨cfg', hr', hinv'⟩ :=
        checkOutput_restore_to_clearInput gen
          stackTarget counter (t :: rest_t) _ cfgR
          hlR htR hstR hcR hscR hiR
          (by have := hinv.h_suffix
              simp only [List.length_cons, List.reverse_reverse] at this ⊢
              rw [← this, List.take_append_drop]) -- take/drop concat
      exact ⟨cfg', TM2Reaches_trans hrR hr', hinv'⟩
    | cons o rest_o =>
      -- Both non-empty
      by_cases heq : t = o
      · -- Heads match: consume and recurse
        subst heq
        obtain ⟨cfg₁, hr₁, hinv₁⟩ :=
          checkOutput_step_match gen stackTarget
            counter t rest_t rest_o cfg hinv
        have hMismatch' : rest_t ≠ rest_o := by
          intro h; apply hMismatch
          rw [h]
        obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
          ih rest_o cfg₁ hinv₁ hMismatch'
        exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, hinv₂⟩
      · -- Heads differ: one TM2 step to checkOutput_restoreTarget
        obtain ⟨cfgR, hrR, hlR, htR, hstR, hcR,
                hscR, hiR⟩ :
            ∃ cfgR : GECfg Γw Γo Q,
              TM2Reaches gen cfg cfgR ∧
              cfgR.l = some GreedyEnumLabel.checkOutput_restoreTarget ∧
              cfgR.stk GreedyEnumStack.target = t :: rest_t ∧
              cfgR.stk GreedyEnumStack.saveTarget =
                (stackTarget.take
                  (stackTarget.length -
                    (t :: rest_t).length)).reverse ∧
              cfgR.stk GreedyEnumStack.counter = counter ∧
              cfgR.stk GreedyEnumStack.saveCounter = [] ∧
              cfgR.stk GreedyEnumStack.input = [] := by
          refine ⟨⟨some GreedyEnumLabel.checkOutput_restoreTarget,
                  { cfg.var with
                    peekTarget := some t
                    peekOut := some o },
                  cfg.stk⟩, ?_, rfl, hinv.h_target,
                hinv.h_saveTarget, hinv.h_counter,
                hinv.h_saveCounter, hinv.h_input⟩
          apply Relation.ReflTransGen.single
          cases cfg with
          | mk l v S =>
            simp only at *
            have hl := hinv.h_label; simp only at hl; subst hl
            have ht := hinv.h_target; simp only at ht
            have ho := hinv.h_output; simp only at ho
            have hne : decide (t = o) = false := by
              simp [heq]
            simp only [GEStep, Turing.TM2.step,
                      greedyEnumMachine, checkOutput,
                      Turing.TM2.stepAux,
                      ht, ho, List.head?,
                      Option.isNone, Bool.and_false,
                      cond_false, Bool.or_false,
                      hne, cond_false]
        obtain ⟨cfg', hr', hinv'⟩ :=
          checkOutput_restore_to_clearInput gen
            stackTarget counter (t :: rest_t) _ cfgR
            hlR htR hstR hcR hscR hiR
            (by have := hinv.h_suffix
                simp only [List.length_cons, List.reverse_reverse] at this ⊢
                rw [← this, List.take_append_drop]) -- take/drop concat
        exact ⟨cfg', TM2Reaches_trans hrR hr', hinv'⟩

end CheckOutputPhase

/-- Once halted, stepNHalt stays fixed. -/
lemma stepNHalt_of_isHalting
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (k : ℕ)
    (hHalt : IsHalting gen (stepNHalt gen cfg k)) :
    stepNHalt gen cfg (k + 1) = stepNHalt gen cfg k := by
  simp only [stepNHalt, IsHalting, step] at *
  -- stepNHalt gen cfg (k+1) = match step gen (stepNHalt gen cfg k) with
  --   | none => stepNHalt gen cfg k | some c' => c'
  -- hHalt : step gen (stepNHalt gen cfg k) = none
  -- so it returns stepNHalt gen cfg k
  simp [hHalt]

lemma stepNHalt_fixed_of_isHalting
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (k m : ℕ)
    (hHalt : IsHalting gen (stepNHalt gen cfg k)) :
    stepNHalt gen cfg (k + m) = stepNHalt gen cfg k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, stepNHalt_of_isHalting]
    · exact ih
    · rwa [ih]

lemma stepNHalt_greedy_inputIndex
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (gcfg : GenConfig Γw Γo Q)
    (n : ℕ)
    (hAlive : ∀ i, i < n →
      ¬IsHalting gen (stepNHalt gen gcfg i)) :
    (stepNHalt gen gcfg n).inputIndex =
      gcfg.inputIndex + n := by
  induction n with
  | zero => simp [stepNHalt]
  | succ n ih =>
    have hAliveN := hAlive n (by omega)
    have ihVal := ih (fun i hi => hAlive i (by omega))
    simp only [IsHalting, step] at hAliveN
    have hne := Option.ne_none_iff_exists'.mp hAliveN
    obtain ⟨gcfg', hStep⟩ := hne
    -- stepNHalt gen gcfg (n+1) unfolds using stepNHalt
    unfold stepNHalt
    simp only [step, hStep]
    -- Now goal should be gcfg'.inputIndex = gcfg.inputIndex + (n + 1)
    -- Extract gen.δ from hStep
    revert hStep
    cases hd : gen.δ
      (stepNHalt gen gcfg n).state
      ((stepNHalt gen gcfg n).input
        (stepNHalt gen gcfg n).inputIndex)
      ((stepNHalt gen gcfg n).work
        (stepNHalt gen gcfg n).workIndex) with
    | none => simp
    | some val =>
      obtain ⟨q', w', o, itd, wd⟩ := val
      have hItd := hGreedy _ _ _ _ _ _ _ _ hd
      subst hItd
      simp only [Option.some.injEq]
      intro hEq
      rw [← hEq, ihVal]
      simp only
      omega

/-- If `stepNHalt gen gcfg n` is halting, there exists a first halting
    step `k ≤ n`, all earlier steps are non-halting, and stepNHalt is
    the same at `k` and `n`. -/
lemma exists_first_halt
    (gen : Generator Γw Γo Q)
    (gcfg : GenConfig Γw Γo Q)
    (n : ℕ)
    (hHalt : IsHalting gen (stepNHalt gen gcfg n)) :
    ∃ k, k ≤ n ∧
      IsHalting gen (stepNHalt gen gcfg k) ∧
      (∀ i, i < k → ¬IsHalting gen (stepNHalt gen gcfg i)) ∧
      stepNHalt gen gcfg n = stepNHalt gen gcfg k := by
  -- The predicate is decidable, so Nat.find works
  have hdec : DecidablePred (fun i => IsHalting gen (stepNHalt gen gcfg i)) := by
    intro i
    simp only [IsHalting, step]
    exact inferInstance
  have hexists : ∃ k, IsHalting gen (stepNHalt gen gcfg k) := ⟨n, hHalt⟩
  let k := Nat.find hexists
  have hk_halt : IsHalting gen (stepNHalt gen gcfg k) :=
    Nat.find_spec hexists
  have hk_min : ∀ i, i < k → ¬IsHalting gen (stepNHalt gen gcfg i) :=
    fun i hi => Nat.find_min hexists hi
  have hk_le : k ≤ n := by
    by_contra h
    push_neg at h
    exact Nat.find_min hexists h hHalt
  have hk_fixed : stepNHalt gen gcfg n = stepNHalt gen gcfg k := by
    have : n = k + (n - k) := (Nat.add_sub_cancel' hk_le).symm
    rw [this]
    exact stepNHalt_fixed_of_isHalting gen gcfg k (n - k) hk_halt
  exact ⟨k, hk_le, hk_halt, hk_min, hk_fixed⟩

-- This will be needed by the caller of runStep_exhausted_not_halted_to_counterIncrement
lemma stepNHalt_preserves_input
    (gen : Generator Γw Γo Q)
    (gcfg : GenConfig Γw Γo Q)
    (n : ℕ) :
    (stepNHalt gen gcfg n).input = gcfg.input := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [stepNHalt]
    cases h : step gen (stepNHalt gen gcfg n) with
    | none => exact ih
    | some c =>
      simp only [step] at h
      revert h
      cases gen.δ _ _ _ with
      | none => simp
      | some val =>
        obtain ⟨q', w', o, itd, wd⟩ := val
        simp only [Option.some.injEq]
        intro h; rw [← h, ih]

lemma copyCounter_to_initRun
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CopyCounterInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      InitRunInvariant target counter cfg' := by
  have hinv₀ : CopyCounterLoopInvariant target counter [] cfg :=
    ⟨hinv.h_label, hinv.h_target, hinv.h_counter, hinv.h_saveCounter,
     hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
  obtain ⟨cfg₁, hr₁, hinv₁⟩ := copyCounter_loop gen target counter [] cfg hinv₀
  simp only [List.append_nil] at hinv₁
  obtain ⟨cfg₂, hr₂, hinv₂⟩ := copyCounter_restore_loop gen target [] counter.reverse cfg₁ hinv₁
  refine ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, ?_⟩
  simp only [List.reverse_reverse, List.append_nil] at hinv₂
  exact hinv₂

lemma initRun_match_halts
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hinv : InitRunInvariant stackTarget counter cfg)
    (hHalt : IsHalting gen
        (stepNHalt gen (initConfig gen (counterToInput counter))
          counter.length))
    (hOut : (stepNHalt gen (initConfig gen (counterToInput counter))
          counter.length).output.reverse = stackTarget) :
    TM2Halts gen cfg := by
  set gcfg₀ := initConfig gen (counterToInput counter)
  set gcfgN := stepNHalt gen gcfg₀ counter.length
  -- Phase 1: initRun → first runStep
  obtain ⟨cfg₁, hr₁, hinv₁⟩ := initRun_to_runStep gen stackTarget counter cfg hinv
  -- Phase 2: find first halting index
  -- Since stepNHalt stops on halt, there exists a first k where it halts
  obtain ⟨k, hk_le, hk_halt, hk_alive⟩ := exists_first_halt gen gcfg₀ counter.length hHalt
-- Phase 3: run loop for k steps (all alive)
  have hk_min := hk_alive.1
  have hk_fixed := hk_alive.2
  have hInitIdx : gcfg₀.inputIndex = 0 := by
    simp [gcfg₀, initConfig]
  obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
    runStep_loop gen hGreedy stackTarget counter gcfg₀ k cfg₁
      hinv₁
      (fun i hi => by
        simp only [hInitIdx, zero_add]
        exact Nat.lt_of_lt_of_le hi hk_le)
      hk_min
  -- Phase 4: at step k, delta returns none → checkOutput
  -- IsHalting means step gen (stepNHalt gen gcfg₀ k) = none,
  -- which means gen.δ on the current state/input/work = none.
  have hk_inputIdx :
      (stepNHalt gen gcfg₀ k).inputIndex = k := by
    rw [stepNHalt_greedy_inputIndex gen hGreedy gcfg₀ k
          hk_min, hInitIdx, Nat.zero_add]
  rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
  · -- Case k < counter.length: halted mid-run, input available
    have hk_input :
        (stepNHalt gen gcfg₀ k).inputIndex
          < counter.length := by
      rw [hk_inputIdx]; exact hk_lt
    have hk_delta : gen.δ
        (stepNHalt gen gcfg₀ k).state
        ((stepNHalt gen gcfg₀ k).input
          (stepNHalt gen gcfg₀ k).inputIndex)
        ((stepNHalt gen gcfg₀ k).work
          (stepNHalt gen gcfg₀ k).workIndex) = none := by
      have h := hk_halt
      simp only [IsHalting, step] at h
      revert h
      cases gen.δ
        (stepNHalt gen gcfg₀ k).state
        ((stepNHalt gen gcfg₀ k).input
          (stepNHalt gen gcfg₀ k).inputIndex)
        ((stepNHalt gen gcfg₀ k).work
          (stepNHalt gen gcfg₀ k).workIndex) with
      | none => intro; rfl
      | some val =>
        obtain ⟨q', w', out?, inDir, workDir⟩ := val
        simp
    obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
      runStep_halted_to_checkOutput gen stackTarget
        counter (stepNHalt gen gcfg₀ k) cfg₂ hinv₂
        hk_input hk_delta
    have hOutK :
        (stepNHalt gen gcfg₀ k).output.reverse
          = stackTarget := by
      have : gcfgN = stepNHalt gen gcfg₀ k := hk_fixed
      rw [this] at hOut; exact hOut
    obtain ⟨cfg₄, hr₄, hhalted⟩ :=
      checkOutput_matching_lists_halt gen stackTarget
        counter stackTarget cfg₃
        (by rw [← hOutK] at hinv₃; rw [← hOutK]
            exact hinv₃)
    exact ⟨cfg₄,
      TM2Reaches_trans
        (TM2Reaches_trans
          (TM2Reaches_trans hr₁ hr₂) hr₃) hr₄,
      hhalted⟩
  · -- Case k = counter.length: input exhausted, final
    -- delta check halts
    have hk_exhausted :
        (stepNHalt gen gcfg₀ k).inputIndex
          = counter.length := by
      rw [hk_inputIdx, hk_eq]
    obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
      runStep_exhausted_halted_to_checkOutput gen
        stackTarget counter
        (stepNHalt gen gcfg₀ k) cfg₂ hinv₂
        hk_exhausted hk_halt
        (by
          rw [stepNHalt_preserves_input]
          simp [gcfg₀, initConfig]
        )
    have hOutK :
        (stepNHalt gen gcfg₀ k).output.reverse
          = stackTarget := by
      have : gcfgN = stepNHalt gen gcfg₀ k := hk_fixed
      rw [this] at hOut; exact hOut
    obtain ⟨cfg₄, hr₄, hhalted⟩ :=
      checkOutput_matching_lists_halt gen stackTarget
        counter stackTarget cfg₃
        (by rw [← hOutK] at hinv₃; rw [← hOutK]
            exact hinv₃)
    exact ⟨cfg₄,
      TM2Reaches_trans
        (TM2Reaches_trans
          (TM2Reaches_trans hr₁ hr₂) hr₃) hr₄,
      hhalted⟩

section CounterIncrement

private structure CounterIncrementLoopInvariant
    (target : List Γo)
    (remaining : List (ULift.{u} Bool))
    (processed : List (ULift.{u} Bool))
    (carry : Bool)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_loop
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = remaining
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = processed
  h_carry       : cfg.var.carry = some carry
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private structure CounterIncrementRestoreInvariant
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = []
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = counter.reverse
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

/-- Increment a bit list with carry (LSB first). -/
private def addCarry : List (ULift.{u} Bool) → Bool → List (ULift.{u} Bool)
  | [], false => []
  | [], true => [ULift.up true]
  | ⟨b⟩ :: rest, c =>
    ⟨Bool.xor b c⟩ :: addCarry rest (b && c)

-- Step 1: counter_increment → counter_increment_loop (one step)
private lemma counter_increment_to_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementLoopInvariant target counter [] true cfg' := by
  -- One TM2 step: load sets carry := some true, goto sets label
  refine ⟨⟨some GreedyEnumLabel.counter_increment_loop,
           { cfg.var with carry := some true },
           cfg.stk⟩, ?_, ?_⟩
  · -- Reachability: one step
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only
      have hl := hinv.h_label
      simp only at hl
      subst hl
      simp [greedyEnumMachine, counter_increment, Turing.TM2.stepAux]
  · -- The invariant holds
    exact ⟨rfl, hinv.h_target, hinv.h_counter, by exact hinv.h_saveCounter, rfl,
           hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩

-- Step 2: loop processes all bits
private lemma counter_increment_loop_to_restore
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (remaining processed : List (ULift.{u} Bool))
    (carry : Bool)
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementLoopInvariant target remaining processed carry cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementRestoreInvariant target
        ((addCarry remaining carry).reverse ++ processed).reverse cfg' := by
  induction remaining generalizing processed carry cfg with
  | nil =>
    -- remaining = [], addCarry [] carry is either [] or [true]
    cases carry with
    | false =>
      -- addCarry [] false = [], so target counter = processed.reverse
      -- One step: peek counter (empty), branch isNone = true, branch carry = false, goto restore
      simp only [addCarry, List.reverse_nil, List.nil_append]
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
               { cfg.var with peekBit := none },
               cfg.stk⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hctr : S GreedyEnumStack.counter = [] := hinv.h_counter
          have hcarry := hinv.h_carry; simp only at hcarry
          simp only [Turing.TM2.step, greedyEnumMachine,
                     counter_increment_loop, Turing.TM2.stepAux]
          rw [hctr]
          simp [List.head?, Option.map, Option.isNone, cond_true, hcarry]
      · exact ⟨rfl, hinv.h_target, hinv.h_counter,
          by simp [List.reverse_reverse, hinv.h_saveCounter],
          hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    | true =>
      -- addCarry [] true = [ULift.up true], push true to saveCounter, goto restore
      simp only [addCarry, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
               { cfg.var with peekBit := none },
               fun k => match k with
                 | GreedyEnumStack.saveCounter => ULift.up true :: processed
                 | other => cfg.stk other⟩, ?_, ?_⟩
      · apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hctr : S GreedyEnumStack.counter = [] := hinv.h_counter
          have hcarry := hinv.h_carry; simp only at hcarry
          have hsc := hinv.h_saveCounter; simp only at hsc
          simp only [Turing.TM2.step, greedyEnumMachine,
                     counter_increment_loop, Turing.TM2.stepAux]
          rw [hctr]
          simp only [Option.isNone, Option.map, List.head?, hcarry, Option.getD_some, cond_true,
            Option.getD_none, Bool.and_true, Bool.bne_true, Bool.not_false, List.tail_nil, ne_eq,
            reduceCtorEq, not_false_eq_true, Function.update_of_ne, Option.some.injEq,
            Turing.TM2.Cfg.mk.injEq, true_and]
          ext k; cases k <;> simp [Function.update, hsc]
      · refine ⟨rfl, ?_, ?_, ?_,
                hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
        · simp [hinv.h_target]
        · simp [hinv.h_counter]
        · simp [List.reverse_cons]
  | cons b rest ih =>
    -- Pop b from counter, compute newBit = xor b.down carry, newCarry = b.down && carry
    -- Push newBit to saveCounter, goto loop with rest, (ULift.up newBit :: processed), newCarry
    cases b with
    | up bv =>
      -- One iteration reaches CounterIncrementLoopInvariant with updated state
      have hone : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
          CounterIncrementLoopInvariant target rest
            (⟨Bool.xor bv carry⟩ :: processed) (bv && carry) cfg₁ := by
        refine ⟨⟨some GreedyEnumLabel.counter_increment_loop,
                 { cfg.var with
                   peekBit := some (Bool.xor bv carry)
                   carry := some (bv && carry) },
                 fun k => match k with
                   | GreedyEnumStack.counter => rest
                   | GreedyEnumStack.saveCounter => ⟨Bool.xor bv carry⟩ :: processed
                   | other => cfg.stk other⟩, ?_, ?_⟩
        · apply Relation.ReflTransGen.single
          cases cfg with
          | mk l v S =>
            have hl := hinv.h_label; simp only at hl; subst hl
            have hctr : S GreedyEnumStack.counter = ⟨bv⟩ :: rest := hinv.h_counter
            have hcarry := hinv.h_carry; simp only at hcarry
            have hsc := hinv.h_saveCounter; simp only at hsc
            simp only [Turing.TM2.step, greedyEnumMachine,
                       counter_increment_loop, Turing.TM2.stepAux]
            rw [hctr]
            simp only [Option.isNone, Option.map, List.head?, hcarry, Option.getD_some,
              List.tail_cons, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
              cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k; cases k <;> simp [Function.update, hsc]
        · exact ⟨rfl, hinv.h_target, rfl, rfl, rfl,
                 hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
      obtain ⟨cfg₁, hreach₁, hinv₁⟩ := hone
      obtain ⟨cfg₂, hreach₂, hinv₂⟩ :=
        ih (⟨Bool.xor bv carry⟩ :: processed) (bv && carry) cfg₁ hinv₁
      refine ⟨cfg₂, TM2Reaches_trans hreach₁ hreach₂, ?_⟩
      -- Need: addCarry (⟨bv⟩ :: rest) carry = ⟨Bool.xor bv carry⟩ :: addCarry rest (bv && carry)
      simp only [addCarry]
      convert hinv₂ using 1
      simp [List.reverse_append, List.reverse_cons, List.reverse_reverse,
            List.append_assoc]

-- Step 3: restore → copyCounter
private structure RestoreLoopInvariant
    (target : List Γo)
    (moved : List (ULift.{u} Bool))
    (rest : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    : Prop where
  h_label       : cfg.l = some GreedyEnumLabel.counter_increment_restore
  h_target      : cfg.stk GreedyEnumStack.target      = target
  h_counter     : cfg.stk GreedyEnumStack.counter     = moved
  h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = rest
  h_input       : cfg.stk GreedyEnumStack.input       = []
  h_workL       : cfg.stk GreedyEnumStack.workL       = []
  h_workR       : cfg.stk GreedyEnumStack.workR       = []
  h_output      : cfg.stk GreedyEnumStack.output      = []
  h_saveTarget  : cfg.stk GreedyEnumStack.saveTarget  = []

private lemma restore_loop
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (moved : List (ULift.{u} Bool))
    (rest : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : RestoreLoopInvariant target moved rest cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target (rest.reverse ++ moved) cfg' := by
  induction rest generalizing moved cfg with
  | nil =>
    -- saveCounter empty: one step (peek, branch true, goto copyCounter)
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨some GreedyEnumLabel.copyCounter,
           { cfg.var with peekBit := none },
           cfg.stk⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        have hl := hinv.h_label
        simp only at hl
        subst hl
        simp only [Turing.TM2.step, greedyEnumMachine,
                    counter_increment_restore, Turing.TM2.stepAux]
        have hsc : S GreedyEnumStack.saveCounter = [] := hinv.h_saveCounter
        rw [hsc]
        simp [List.head?, Option.map, Option.isNone]
    · simp only [List.reverse_nil, List.nil_append]
      exact ⟨rfl, hinv.h_target, hinv.h_counter, hinv.h_input,
            hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget, hinv.h_saveCounter⟩
  | cons b rest' ih =>
    -- After one loop iteration, we have RestoreLoopInvariant with (b :: moved) and rest'
    -- Then ih gives us the result
    -- First show one iteration
    obtain ⟨cfg₁, hreach₁, hinv₁⟩ : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        RestoreLoopInvariant target (b :: moved) rest' cfg₁ := by
      refine ⟨⟨some GreedyEnumLabel.counter_increment_restore,
                  { cfg.var with peekBit := some b.down },
                  fun k => match k with
                    | GreedyEnumStack.counter => b :: moved
                    | GreedyEnumStack.saveCounter => rest'
                    | other => cfg.stk other⟩, ?_, ?_⟩
      · -- One TM2 step
        apply Relation.ReflTransGen.single
        cases cfg with
        | mk l v S =>
          have hl := hinv.h_label; simp only at hl; subst hl
          have hsc : S GreedyEnumStack.saveCounter = b :: rest' := hinv.h_saveCounter
          have hc : S GreedyEnumStack.counter = moved := hinv.h_counter
          simp only [Turing.TM2.step, greedyEnumMachine,
                    counter_increment_restore, Turing.TM2.stepAux]
          rw [hsc]
          cases b with
          | up bv =>
            simp only [Option.isNone, Option.map, List.head?, List.tail_cons,
              Option.getD_some, ne_eq, reduceCtorEq, not_false_eq_true, Function.update_of_ne,
              cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
            ext k
            cases k <;> simp [Function.update, hc]
      · -- The invariant holds
        exact ⟨rfl, hinv.h_target, rfl, rfl,
              hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
    obtain ⟨cfg₂, hreach₂, hinv₂⟩ := ih (b :: moved) cfg₁ hinv₁
    refine ⟨cfg₂, TM2Reaches_trans hreach₁ hreach₂, ?_⟩
    -- rest'.reverse ++ (b :: moved) = (b :: rest').reverse ++ moved
    rwa [List.reverse_cons, List.append_assoc, List.singleton_append]

private lemma counter_increment_restore_to_copyCounter
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementRestoreInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target counter cfg' := by
  have hinv' : RestoreLoopInvariant target [] counter.reverse cfg :=
    ⟨hinv.h_label, hinv.h_target, hinv.h_counter, hinv.h_saveCounter,
     hinv.h_input, hinv.h_workL, hinv.h_workR, hinv.h_output, hinv.h_saveTarget⟩
  obtain ⟨cfg', hreach, hcopy⟩ := restore_loop gen target [] counter.reverse cfg hinv'
  refine ⟨cfg', hreach, ?_⟩
  simp only [List.reverse_reverse, List.append_nil] at hcopy
  exact hcopy

private lemma addCarry_false (l : List (ULift.{u} Bool)) :
    addCarry l false = l := by
  induction l with
  | nil => simp [addCarry]
  | cons b rest ih =>
    cases b with
    | up b => cases b <;> simp [addCarry, Bool.xor, ih]

private lemma counterIncrement_eq_addCarry (counter : List (ULift.{u} Bool)) :
    counterIncrement counter = addCarry counter true := by
  induction counter with
  | nil => simp [counterIncrement, addCarry]
  | cons b rest ih =>
    cases b with
    | up b =>
      cases b <;> simp [counterIncrement, addCarry, Bool.xor, addCarry_false, *]

lemma counter_increment_to_copyCounter
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q))
    (hinv : CounterIncrementInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant target (counterIncrement counter) cfg' := by
  -- Step 1: counter_increment → counter_increment_loop
  obtain ⟨cfg₁, hreach₁, hinv₁⟩ := counter_increment_to_loop gen target counter cfg hinv
  -- Step 2: loop processes all bits
  obtain ⟨cfg₂, hreach₂, hinv₂⟩ :=
    counter_increment_loop_to_restore gen target counter [] true cfg₁ hinv₁
  -- Simplify the counter expression in hinv₂
  simp only [List.append_nil, List.reverse_reverse] at hinv₂
  -- Step 3: restore → copyCounter
  obtain ⟨cfg₃, hreach₃, hinv₃⟩ :=
    counter_increment_restore_to_copyCounter gen target _ cfg₂ hinv₂
  -- Chain reachability and rewrite counter
  refine ⟨cfg₃, ?_, ?_⟩
  · exact TM2Reaches_trans (TM2Reaches_trans hreach₁ hreach₂) hreach₃
  · rwa [counterIncrement_eq_addCarry]

end CounterIncrement


section ClearPhase

private lemma clear_stack_input
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (input : List (ULift.{u} Bool))
    (workL : List Γw) (workR : List Γw)
    (output : List Γo)
    (cfg : GECfg Γw Γo Q)
    (h_label : cfg.l = some GreedyEnumLabel.clearInput)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = input)
    (h_workL : cfg.stk GreedyEnumStack.workL = workL)
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = output)
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearWorkL ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = workL ∧
      cfg'.stk GreedyEnumStack.workR = workR ∧
      cfg'.stk GreedyEnumStack.output = output ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction input generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearWorkL,
             { cfg.var with peekBit := none },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hi : S GreedyEnumStack.input = [] := h_input
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearInput, Turing.TM2.stepAux]
      rw [hi]
      simp [List.head?, Option.map, Option.isNone, cond_true]
  | cons b rest ih =>
    -- One step: peek input (non-empty), branch, pop, goto clearInput
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearInput ∧
        cfg₁.stk GreedyEnumStack.input = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.workL = workL ∧
        cfg₁.stk GreedyEnumStack.workR = workR ∧
        cfg₁.stk GreedyEnumStack.output = output ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearInput,
               { cfg.var with peekBit := some b.down },
               fun k => match k with
                 | GreedyEnumStack.input => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_workL, h_workR,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hi : S GreedyEnumStack.input = b :: rest := h_input
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearInput, Turing.TM2.stepAux]
        rw [hi]
        cases b with
        | up bv =>
          simp only [Option.isNone, Option.map, List.head?, List.tail_cons,
            cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
          ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hi₁, ht₁, hc₁, hwl₁, hwr₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_workL
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (workL : List Γw) (workR : List Γw)
    (output : List Γo)
    (cfg : GECfg Γw Γo Q)
    (h_label : cfg.l = some GreedyEnumLabel.clearWorkL)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = workL)
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = output)
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearWorkR ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = [] ∧
      cfg'.stk GreedyEnumStack.workR = workR ∧
      cfg'.stk GreedyEnumStack.output = output ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction workL generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearWorkR,
             { cfg.var with peekBit := some false },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hwl : S GreedyEnumStack.workL = [] := h_workL
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearWorkL, Turing.TM2.stepAux]
      rw [hwl]
      simp [List.head?, Option.isSome, BEq.beq]
      rfl
  | cons w rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearWorkL ∧
        cfg₁.stk GreedyEnumStack.workL = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.input = [] ∧
        cfg₁.stk GreedyEnumStack.workR = workR ∧
        cfg₁.stk GreedyEnumStack.output = output ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearWorkL,
               { cfg.var with peekBit := some true },
               fun k => match k with
                 | GreedyEnumStack.workL => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_input, h_workR,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hwl : S GreedyEnumStack.workL = w :: rest := h_workL
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearWorkL, Turing.TM2.stepAux]
        rw [hwl]
        simp only [Option.isSome, List.head?, Option.some_beq_some, beq_false,
          Bool.not_true, List.tail_cons, cond_false,
              Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        have : Option.instBEq.beq (some true) (some false) = false := by decide
        ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hwl₁, ht₁, hc₁, hi₁, hwr₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_workR
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (workR : List Γw)
    (output : List Γo)
    (cfg : GECfg Γw Γo Q)
    (h_label : cfg.l = some GreedyEnumLabel.clearWorkR)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = [])
    (h_workR : cfg.stk GreedyEnumStack.workR = workR)
    (h_output : cfg.stk GreedyEnumStack.output = output)
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      cfg'.l = some GreedyEnumLabel.clearOutput ∧
      cfg'.stk GreedyEnumStack.target = target ∧
      cfg'.stk GreedyEnumStack.counter = counter ∧
      cfg'.stk GreedyEnumStack.input = [] ∧
      cfg'.stk GreedyEnumStack.workL = [] ∧
      cfg'.stk GreedyEnumStack.workR = [] ∧
      cfg'.stk GreedyEnumStack.output = output ∧
      cfg'.stk GreedyEnumStack.saveTarget = [] ∧
      cfg'.stk GreedyEnumStack.saveCounter = [] := by
  induction workR generalizing cfg with
  | nil =>
    refine ⟨⟨some GreedyEnumLabel.clearOutput,
             { cfg.var with peekBit := some false },
             cfg.stk⟩, ?_, rfl, h_target, h_counter, h_input, h_workL, h_workR,
             h_output, h_saveTarget, h_saveCounter⟩
    apply Relation.ReflTransGen.single
    cases cfg with
    | mk l v S =>
      simp only at h_label; subst h_label
      have hwr : S GreedyEnumStack.workR = [] := h_workR
      simp only [Turing.TM2.step, greedyEnumMachine,
                 clearWorkR, Turing.TM2.stepAux, hwr, List.head?, Option.isSome,
                 BEq.beq]
      rw [show Option.instBEq.beq (some false) (some false) = true from by decide]
      simp [cond_true]
  | cons w rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearWorkR ∧
        cfg₁.stk GreedyEnumStack.workR = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.input = [] ∧
        cfg₁.stk GreedyEnumStack.workL = [] ∧
        cfg₁.stk GreedyEnumStack.output = output ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearWorkR,
               { cfg.var with peekBit := some true },
               fun k => match k with
                 | GreedyEnumStack.workR => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter, h_input, h_workL,
              h_output, h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have hwr : S GreedyEnumStack.workR = w :: rest := h_workR
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearWorkR, Turing.TM2.stepAux, hwr, List.head?,
                   Option.isSome, List.tail_cons, BEq.beq]
        rw [show Option.instBEq.beq (some true) (some false) = false from by decide]
        simp only [cond_false, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
        ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, hwr₁, ht₁, hc₁, hi₁, hwl₁, ho₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, h₂⟩ := ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, h₂⟩

private lemma clear_stack_output
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (output : List Γo)
    (cfg : GECfg Γw Γo Q)
    (h_label : cfg.l = some GreedyEnumLabel.clearOutput)
    (h_target : cfg.stk GreedyEnumStack.target = target)
    (h_counter : cfg.stk GreedyEnumStack.counter = counter)
    (h_input : cfg.stk GreedyEnumStack.input = [])
    (h_workL : cfg.stk GreedyEnumStack.workL = [])
    (h_workR : cfg.stk GreedyEnumStack.workR = [])
    (h_output : cfg.stk GreedyEnumStack.output = output)
    (h_saveTarget : cfg.stk GreedyEnumStack.saveTarget = [])
    (h_saveCounter : cfg.stk GreedyEnumStack.saveCounter = []) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementInvariant target counter cfg' := by
  induction output generalizing cfg with
  | nil =>
    -- Same as old clear_stack_output: peek empty → goto counter_increment
    refine ⟨⟨some GreedyEnumLabel.counter_increment,
             { cfg.var with peekOut := none },
             cfg.stk⟩, ?_, ?_⟩
    · apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearOutput, Turing.TM2.stepAux,
                   List.head?, Option.isNone]
        simp only [] at h_output
        rw [h_output]
        simp
    · exact ⟨rfl, h_target, h_counter, h_input,
             h_workL, h_workR, h_output, h_saveTarget,
             h_saveCounter⟩
  | cons o rest ih =>
    have hstep : ∃ cfg₁, TM2Reaches gen cfg cfg₁ ∧
        cfg₁.l = some GreedyEnumLabel.clearOutput ∧
        cfg₁.stk GreedyEnumStack.output = rest ∧
        cfg₁.stk GreedyEnumStack.target = target ∧
        cfg₁.stk GreedyEnumStack.counter = counter ∧
        cfg₁.stk GreedyEnumStack.input = [] ∧
        cfg₁.stk GreedyEnumStack.workL = [] ∧
        cfg₁.stk GreedyEnumStack.workR = [] ∧
        cfg₁.stk GreedyEnumStack.saveTarget = [] ∧
        cfg₁.stk GreedyEnumStack.saveCounter = [] := by
      refine ⟨⟨some GreedyEnumLabel.clearOutput,
               { cfg.var with peekOut := some o },
               fun k => match k with
                 | GreedyEnumStack.output => rest
                 | other => cfg.stk other⟩,
              ?_, rfl, rfl, h_target, h_counter,
              h_input, h_workL, h_workR,
              h_saveTarget, h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at h_label; subst h_label
        have ho : S GreedyEnumStack.output = o :: rest :=
          h_output
        simp only [Turing.TM2.step, greedyEnumMachine,
                   clearOutput, Turing.TM2.stepAux, ho,
                   List.head?, Option.isNone, List.tail_cons,
                   cond_false, Option.some.injEq,
                   Turing.TM2.Cfg.mk.injEq, true_and]
        ext k; cases k <;> simp [Function.update]
    obtain ⟨cfg₁, hr₁, hl₁, ho₁, ht₁, hc₁, hi₁,
            hwl₁, hwr₁, hst₁, hsc₁⟩ := hstep
    obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
      ih cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁ ho₁ hst₁ hsc₁
    exact ⟨cfg₂, TM2Reaches_trans hr₁ hr₂, hinv₂⟩

lemma clearInput_to_counterIncrement
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hinv : ClearInputInvariant target counter cfg) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementInvariant target counter cfg' := by
  obtain ⟨cfg₁, hr₁, hl₁, ht₁, hc₁, hi₁,
          hwl₁, hwr₁, ho₁, hst₁, hsc₁⟩ :=
    clear_stack_input gen target counter
      (cfg.stk GreedyEnumStack.input)
      (cfg.stk GreedyEnumStack.workL)
      (cfg.stk GreedyEnumStack.workR)
      (cfg.stk GreedyEnumStack.output)
      cfg hinv.h_label hinv.h_target hinv.h_counter
      rfl rfl rfl rfl
      hinv.h_saveTarget hinv.h_saveCounter
  obtain ⟨cfg₂, hr₂, hl₂, ht₂, hc₂, hi₂,
          hwl₂, hwr₂, ho₂, hst₂, hsc₂⟩ :=
    clear_stack_workL gen target counter
      (cfg.stk GreedyEnumStack.workL)
      (cfg.stk GreedyEnumStack.workR)
      (cfg.stk GreedyEnumStack.output)
      cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁
      ho₁ hst₁ hsc₁
  obtain ⟨cfg₃, hr₃, hl₃, ht₃, hc₃, hi₃,
          hwl₃, hwr₃, ho₃, hst₃, hsc₃⟩ :=
    clear_stack_workR gen target counter
      (cfg.stk GreedyEnumStack.workR)
      (cfg.stk GreedyEnumStack.output)
      cfg₂ hl₂ ht₂ hc₂ hi₂ hwl₂ hwr₂
      ho₂ hst₂ hsc₂
  obtain ⟨cfg₄, hr₄, hinv₄⟩ :=
    clear_stack_output gen target counter
      (cfg₃.stk GreedyEnumStack.output)
      cfg₃ hl₃ ht₃ hc₃ hi₃ hwl₃ hwr₃
      rfl hst₃ hsc₃
  exact ⟨cfg₄,
    TM2Reaches_trans
      (TM2Reaches_trans
        (TM2Reaches_trans hr₁ hr₂) hr₃) hr₄,
    hinv₄⟩

end ClearPhase

section NoMatchPhase

/-- When input is exhausted and generator did NOT halt,
    runStep goes to clearWorkL (via the "input empty" branch).
    This eventually reaches clearInput → counterIncrement. -/
private lemma runStep_exhausted_not_halted_to_counterIncrement
    (gen : Generator Γw Γo Q)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (gcfg : GenConfig Γw Γo Q)
    (cfg : GECfg Γw Γo Q)
    (hinv : RunStepInvariant gen stackTarget counter gcfg cfg)
    (hExhausted : gcfg.inputIndex = counter.length)
    (hNotHalted : ¬IsHalting gen gcfg)
    (hInput : gcfg.input = counterToInput counter)
     :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CounterIncrementInvariant stackTarget counter cfg' := by
  -- Extract that input stack is empty
  have hInputEmpty : cfg.stk GreedyEnumStack.input = [] := by
    rw [hinv.h_input, hExhausted, List.drop_length]
  -- Extract that gen.δ returns some (not halted)
  have hDeltaNe : gen.δ gcfg.state
      (gcfg.input gcfg.inputIndex)
      (gcfg.work gcfg.workIndex) ≠ none := by
    intro h
    apply hNotHalted
    simp only [IsHalting, step, h]
  obtain ⟨⟨q', w', o, itd, wd⟩, hDelta⟩ :=
    Option.ne_none_iff_exists'.mp hDeltaNe
  -- Part A: reach clearWorkL via modified runStep
  obtain ⟨cfgCW, hrCW, hlCW, htCW, hcCW, hiCW,
          hoCW, hstCW, hscCW⟩ :
      ∃ cfgCW : GECfg Γw Γo Q,
        TM2Reaches gen cfg cfgCW ∧
        cfgCW.l = some GreedyEnumLabel.clearWorkL ∧
        cfgCW.stk GreedyEnumStack.target
          = stackTarget ∧
        cfgCW.stk GreedyEnumStack.counter = counter ∧
        cfgCW.stk GreedyEnumStack.input = [] ∧
        cfgCW.stk GreedyEnumStack.output
          = gcfg.output.reverse ∧
        cfgCW.stk GreedyEnumStack.saveTarget = [] ∧
        cfgCW.stk GreedyEnumStack.saveCounter = [] := by
    -- The modified runStep when input is empty:
    -- 1. peek input → none, inputBit := false
    -- 2. branch peekBit == some false → true
    -- 3. peek workR
    -- 4. [pop workR if non-empty]
    -- 5. applyDelta with inputBit=false
    -- 6. transHalted = false → goto clearWorkL
    --
    -- applyDelta uses gen.δ with inputBit=false and
    -- the current head symbol. hDelta tells us gen.δ
    -- returns some, so transHalted = false.
    --
    -- All of runStep's internal peek/branch/pop/load
    -- execute within a single Turing.TM2.step call.
    -- Case split on workR empty vs non-empty.
    cases hWR : cfg.stk GreedyEnumStack.workR with
    | nil =>
      -- workR empty: peek gets none, no pop, applyDelta,
      -- transHalted = false → goto clearWorkL
      have hBlank : gcfg.work gcfg.workIndex = gen.blank := by
        have := hinv.h_work.2.1 0 (by simp [hWR])
        simp only [CharP.cast_eq_zero, add_zero] at this
        exact this
      refine ⟨⟨some GreedyEnumLabel.clearWorkL,
               applyDelta gen
                 { transQ := cfg.var.transQ
                   transW := gen.blank
                   transWDir := cfg.var.transWDir
                   transOut := cfg.var.transOut
                   transHalted := cfg.var.transHalted
                   inputBit := false
                   carry := cfg.var.carry
                   peekBit := some false
                   peekTarget := cfg.var.peekTarget
                   peekOut := cfg.var.peekOut },
               cfg.stk⟩, ?_, rfl,
             hinv.h_target, hinv.h_counter, hInputEmpty,
             hinv.h_output, hinv.h_saveTarget,
             hinv.h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hQ := hinv.h_transQ; simp only at hQ
        have hInputBit :
            gcfg.input gcfg.inputIndex = false := by
          rw [hInput, hExhausted]
          simp [counterToInput]
        rw [hInputBit, hBlank] at hDelta
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine, runStep,
                   Turing.TM2.stepAux,
                   hInputEmpty, hWR, List.head?,
                   Option.isSome,
                   Option.getD, BEq.beq,
                   cond_false,
                   applyDelta, hQ,
                   hDelta, List.tail_nil]
        have h1 : Option.instBEq.beq (some false) (some false) = true := by decide
        have h2 : Option.instBEq.beq (some false) (some true) = false := by decide
        rw [h1, h2, cond_true, cond_false]
    | cons w rest =>
      -- workR non-empty: peek gets some w, pop w,
      -- applyDelta, transHalted = false → goto clearWorkL
      have hHead : w = gcfg.work gcfg.workIndex := by
        have := hinv.h_work.1 0 (by simp [hWR])
        simp only [List.get_eq_getElem, hWR, List.getElem_cons_zero,
          CharP.cast_eq_zero, add_zero] at this
        exact this
      refine ⟨⟨some GreedyEnumLabel.clearWorkL,
               applyDelta gen
                 { transQ := cfg.var.transQ
                   transW := w
                   transWDir := cfg.var.transWDir
                   transOut := cfg.var.transOut
                   transHalted := cfg.var.transHalted
                   inputBit := false
                   carry := cfg.var.carry
                   peekBit := some true
                   peekTarget := cfg.var.peekTarget
                   peekOut := cfg.var.peekOut },
               fun k => match k with
                 | GreedyEnumStack.workR => rest
                 | other => cfg.stk other⟩, ?_, rfl,
             hinv.h_target, hinv.h_counter, hInputEmpty,
             hinv.h_output, hinv.h_saveTarget,
             hinv.h_saveCounter⟩
      apply Relation.ReflTransGen.single
      cases cfg with
      | mk l v S =>
        simp only at *
        have hl := hinv.h_label; simp only at hl; subst hl
        have hQ := hinv.h_transQ; simp only at hQ
        have hInputBit :
            gcfg.input gcfg.inputIndex = false := by
          rw [hInput, hExhausted]
          simp [counterToInput]
        rw [hInputBit] at hDelta
        simp only [GEStep, Turing.TM2.step,
                   greedyEnumMachine, runStep,
                   Turing.TM2.stepAux,
                   hInputEmpty, hWR, List.head?,
                   Option.isSome,
                   Option.getD, BEq.beq,
                   List.tail_cons,
                   applyDelta, hQ,
                   List.tail_nil]
        have h1 : Option.instBEq.beq (some false) (some false) = true := by decide
        have h2 : Option.instBEq.beq (some true) (some true) = true := by decide
        rw [h1, h2, cond_true, cond_true]
        -- Now need to show the stk functions match
        simp only [Option.some.injEq]
        rw [hHead, hDelta]
        simp only [cond_false, Turing.TM2.Cfg.mk.injEq,
                   true_and]
        ext k; cases k <;> simp [Function.update]
  -- Part B: chain clears to CounterIncrementInvariant
  obtain ⟨cfg₁, hr₁, hl₁, ht₁, hc₁, hi₁,
          hwl₁, hwr₁, ho₁, hst₁, hsc₁⟩ :=
    clear_stack_workL gen stackTarget counter
      (cfgCW.stk GreedyEnumStack.workL)
      (cfgCW.stk GreedyEnumStack.workR)
      gcfg.output.reverse
      cfgCW hlCW htCW hcCW hiCW rfl rfl
      hoCW hstCW hscCW
  obtain ⟨cfg₂, hr₂, hl₂, ht₂, hc₂, hi₂,
          hwl₂, hwr₂, ho₂, hst₂, hsc₂⟩ :=
    clear_stack_workR gen stackTarget counter
      (cfgCW.stk GreedyEnumStack.workR)
      gcfg.output.reverse
      cfg₁ hl₁ ht₁ hc₁ hi₁ hwl₁ hwr₁
      ho₁ hst₁ hsc₁
  obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
    clear_stack_output gen stackTarget counter
      (cfg₂.stk GreedyEnumStack.output)
      cfg₂ hl₂ ht₂ hc₂ hi₂ hwl₂ hwr₂
      rfl hst₂ hsc₂
  exact ⟨cfg₃,
    TM2Reaches_trans
      (TM2Reaches_trans
        (TM2Reaches_trans hrCW hr₁) hr₂) hr₃,
    hinv₃⟩

end NoMatchPhase

lemma eval_dom_iff_TM2Halts
    (gen : Generator Γw Γo Q) (target : List Γo) :
    (@Turing.TM2.eval.{u,u,u,u} GreedyEnumStack (stackAlphabet Γw Γo Q)
      GreedyEnumLabel (GreedyEnumSigma Γw Γo Q) _ _ _
      (greedyEnumMachine gen) GreedyEnumStack.target target).Dom ↔
    TM2Halts gen (Turing.TM2.init GreedyEnumStack.target target) := by
  change (Turing.eval (GEStep gen) _).Dom ↔ _
  constructor
  · intro h
    obtain ⟨cfg', hcfg'⟩ := Part.dom_iff_mem.mp h
    rw [Turing.mem_eval] at hcfg'
    exact ⟨cfg', hcfg'.1, hcfg'.2⟩
  · intro ⟨cfg', h1, h2⟩
    exact Part.dom_iff_mem.mpr ⟨cfg', Turing.mem_eval.mpr ⟨h1, h2⟩⟩

lemma init_copyCounterInvariant
    (_ : Generator Γw Γo Q) -- Keep this to help with universe level pinning.
    (target : List Γo) :
    CopyCounterInvariant target []
      (@Turing.TM2.init GreedyEnumStack.{u}
        (stackAlphabet Γw Γo Q)
        GreedyEnumLabel.{u}
        (GreedyEnumSigma Γw Γo Q)
        _ _ _
        GreedyEnumStack.target target) := by
  exact ⟨rfl, by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update],
    by simp [Turing.TM2.init, Function.update]⟩

lemma initRun_no_match_to_copyCounter
    (gen : Generator Γw Γo Q)
    (hGreedy : gen.IsGreedy)
    (stackTarget : List Γo)
    (counter : List (ULift.{u} Bool))
    (cfg : GECfg Γw Γo Q)
    (hinv : InitRunInvariant stackTarget counter cfg)
    (hNoMatch : counterEnumStep gen stackTarget.reverse
        counter ≠ none) :
    ∃ cfg', TM2Reaches gen cfg cfg' ∧
      CopyCounterInvariant stackTarget
        (counterIncrement counter) cfg' := by
  set gcfg₀ := initConfig gen (counterToInput counter)
  set gcfgN := stepNHalt gen gcfg₀ counter.length
  -- Phase 1: initRun → runStep
  obtain ⟨cfg₁, hr₁, hinv₁⟩ :=
    initRun_to_runStep gen stackTarget counter cfg hinv
  have hInitIdx : gcfg₀.inputIndex = 0 := by
    simp [gcfg₀, initConfig]
  -- Case split: does the generator halt within counter.length steps?
  by_cases hHalt : IsHalting gen gcfgN
  · -- Case A: generator halts at some step k ≤ counter.length
    -- But output doesn't match (from hNoMatch)
    obtain ⟨k, hk_le, hk_halt, hk_min, hk_fixed⟩ :=
      exists_first_halt gen gcfg₀ counter.length hHalt
    -- Run loop for k steps
    obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
      runStep_loop gen hGreedy stackTarget counter
        gcfg₀ k cfg₁ hinv₁
        (fun i hi => by
          simp only [hInitIdx, zero_add]
          exact Nat.lt_of_lt_of_le hi hk_le)
        hk_min
    -- Reach checkOutput (case split k < length vs k = length)
    have hk_inputIdx :
        (stepNHalt gen gcfg₀ k).inputIndex = k := by
      rw [stepNHalt_greedy_inputIndex gen hGreedy
            gcfg₀ k hk_min, hInitIdx, Nat.zero_add]
    rcases Nat.lt_or_eq_of_le hk_le with hk_lt | hk_eq
    · -- k < counter.length: halted mid-run
      have hk_input :
          (stepNHalt gen gcfg₀ k).inputIndex
            < counter.length := by
        rw [hk_inputIdx]; exact hk_lt
      have hk_delta : gen.δ
          (stepNHalt gen gcfg₀ k).state
          ((stepNHalt gen gcfg₀ k).input
            (stepNHalt gen gcfg₀ k).inputIndex)
          ((stepNHalt gen gcfg₀ k).work
            (stepNHalt gen gcfg₀ k).workIndex)
          = none := by
        have h := hk_halt
        simp only [IsHalting, step] at h
        revert h
        cases gen.δ
          (stepNHalt gen gcfg₀ k).state
          ((stepNHalt gen gcfg₀ k).input
            (stepNHalt gen gcfg₀ k).inputIndex)
          ((stepNHalt gen gcfg₀ k).work
            (stepNHalt gen gcfg₀ k).workIndex) with
        | none => intro; rfl
        | some val =>
          obtain ⟨q', w', out?, inDir, workDir⟩ := val
          simp
      obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
        runStep_halted_to_checkOutput gen stackTarget
          counter (stepNHalt gen gcfg₀ k) cfg₂ hinv₂
          hk_input hk_delta
      have hOutputMismatch :
          stackTarget ≠
            (stepNHalt gen gcfg₀ k).output.reverse := by
        intro heq
        apply hNoMatch
        rw [← hk_fixed] at hk_halt
        exact (counterEnumStep_eq_none_iff gen
          stackTarget.reverse counter).mpr
          ⟨hk_halt, by
            rw [heq, hk_fixed, List.reverse_reverse]
          ⟩
      obtain ⟨cfg₄, hr₄, hinv₄⟩ :=
        checkOutput_mismatch_to_clearInput gen
          stackTarget counter stackTarget
          (stepNHalt gen gcfg₀ k).output.reverse
          cfg₃ hinv₃ hOutputMismatch
      obtain ⟨cfg₅, hr₅, hinv₅⟩ :=
        clearInput_to_counterIncrement gen stackTarget
          counter cfg₄ hinv₄
      obtain ⟨cfg₆, hr₆, hinv₆⟩ :=
        counter_increment_to_copyCounter gen stackTarget
          counter cfg₅ hinv₅
      exact ⟨cfg₆,
        TM2Reaches_trans
          (TM2Reaches_trans
            (TM2Reaches_trans
              (TM2Reaches_trans
                (TM2Reaches_trans hr₁ hr₂) hr₃)
              hr₄) hr₅) hr₆,
        hinv₆⟩
    · -- k = counter.length: exhausted then halted
      have hk_exhausted :
          (stepNHalt gen gcfg₀ k).inputIndex
            = counter.length := by
        rw [hk_inputIdx, hk_eq]
      obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
        runStep_exhausted_halted_to_checkOutput gen
          stackTarget counter
          (stepNHalt gen gcfg₀ k) cfg₂ hinv₂
          hk_exhausted hk_halt
          (by rw [stepNHalt_preserves_input];
              simp [gcfg₀, initConfig])
      have hOutputMismatch :
          stackTarget ≠
            (stepNHalt gen gcfg₀ k).output.reverse := by
        intro heq
        apply hNoMatch
        have hk_halt' : IsHalting gen gcfgN := by
          change IsHalting gen
            (stepNHalt gen gcfg₀ counter.length)
          rw [hk_fixed]; exact hk_halt
        exact (counterEnumStep_eq_none_iff gen
          stackTarget.reverse counter).mpr
          ⟨hk_halt', by
            rw [hk_fixed, heq, List.reverse_reverse]⟩
      obtain ⟨cfg₄, hr₄, hinv₄⟩ :=
        checkOutput_mismatch_to_clearInput gen
          stackTarget counter stackTarget
          (stepNHalt gen gcfg₀ k).output.reverse
          cfg₃ hinv₃ hOutputMismatch
      obtain ⟨cfg₅, hr₅, hinv₅⟩ :=
        clearInput_to_counterIncrement gen stackTarget
          counter cfg₄ hinv₄
      obtain ⟨cfg₆, hr₆, hinv₆⟩ :=
        counter_increment_to_copyCounter gen stackTarget
          counter cfg₅ hinv₅
      exact ⟨cfg₆,
        TM2Reaches_trans
          (TM2Reaches_trans
            (TM2Reaches_trans
              (TM2Reaches_trans
                (TM2Reaches_trans hr₁ hr₂) hr₃)
              hr₄) hr₅) hr₆,
        hinv₆⟩
  · -- Case B: generator doesn't halt within counter.length steps
    -- Run loop for counter.length steps
    obtain ⟨cfg₂, hr₂, hinv₂⟩ :=
      runStep_loop gen hGreedy stackTarget counter
        gcfg₀ counter.length cfg₁ hinv₁
        (fun i hi => by
          simp only [hInitIdx, zero_add]; exact hi)
        (fun i hi => by
          -- stepNHalt gen gcfg₀ i can't be halting
          -- for any i < counter.length, because if it
          -- were, gcfgN would also be halting
          -- (contradicting hHalt)
          intro habs
          exact hHalt (by
            have := stepNHalt_fixed_of_isHalting gen gcfg₀ i
              (counter.length - i) habs
            rw [Nat.add_sub_cancel' (Nat.le_of_lt hi)] at this
            change IsHalting gen (stepNHalt gen gcfg₀ counter.length)
            rw [this]
            exact habs
            )
          )
    -- Input exhausted, not halted → counterIncrement
    have hExhausted :
        (stepNHalt gen gcfg₀ counter.length).inputIndex
          = counter.length := by
      rw [stepNHalt_greedy_inputIndex gen hGreedy gcfg₀
            counter.length
            (fun i hi => by
              intro habs; exact hHalt (by
                have := stepNHalt_fixed_of_isHalting gen gcfg₀ i
                  (counter.length - i) habs
                rw [Nat.add_sub_cancel' (Nat.le_of_lt hi)] at this
                change IsHalting gen (stepNHalt gen gcfg₀ counter.length)
                rw [this]
                exact habs
              )
          ),
          hInitIdx, Nat.zero_add]
    obtain ⟨cfg₃, hr₃, hinv₃⟩ :=
      runStep_exhausted_not_halted_to_counterIncrement
        gen stackTarget counter
        (stepNHalt gen gcfg₀ counter.length) cfg₂ hinv₂
        hExhausted
        (by exact hHalt)
        (by rw [stepNHalt_preserves_input];
            simp [gcfg₀, initConfig])
    obtain ⟨cfg₄, hr₄, hinv₄⟩ :=
      counter_increment_to_copyCounter gen stackTarget
        counter cfg₃ hinv₃
    exact ⟨cfg₄,
      TM2Reaches_trans
        (TM2Reaches_trans
          (TM2Reaches_trans hr₁ hr₂) hr₃) hr₄,
      hinv₄⟩

end GreedyEnum

end RandomisedGeneration
