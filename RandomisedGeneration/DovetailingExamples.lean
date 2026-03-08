import RandomisedGeneration.GeneratorExamples
import RandomisedGeneration.TM2RecognitionByGeneratorSimulation

namespace RandomisedGeneration

namespace DovetailingExamples
set_option linter.style.longLine false
set_option linter.hashCommand false

deriving instance Repr for DovetailStack
deriving instance Repr for DovetailLabel
deriving instance Repr for InputTapeDirection
deriving instance Repr for WorkTapeDirection
deriving instance Repr for DovetailSigma

namespace SimpleGenerator

-- [] is recognised: the all-zeros input halts immediately with empty output
example : DovetailRecognises GeneratorExamples.simpleGenerator [] := by
  rw [DovetailRecognises_iff_Computes]
  exact ⟨fun _ => false, Computes.halt _ (by
    simp [step, GeneratorExamples.simpleGenerator, initConfig])⟩

-- [1] is recognised: input 1,0,0,... produces [1] then halts
example : DovetailRecognises GeneratorExamples.simpleGenerator [1] := by
  rw [DovetailRecognises_iff_Computes]
  refine ⟨fun n => n = 0, ?_⟩
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator, initConfig]; rfl)
  apply Computes.halt
  simp [step, GeneratorExamples.simpleGenerator]

-- [1, 1] is recognised: input 1,1,0,... produces [1,1] then halts
example : DovetailRecognises GeneratorExamples.simpleGenerator [1, 1] := by
  rw [DovetailRecognises_iff_Computes]
  refine ⟨fun n => n < 2, ?_⟩
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator]; rfl)
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator]; rfl)
  apply Computes.halt
  simp [step, GeneratorExamples.simpleGenerator, initConfig]

-- [1, 1, 1] is recognised
example : DovetailRecognises GeneratorExamples.simpleGenerator [1, 1, 1] := by
  rw [DovetailRecognises_iff_Computes]
  refine ⟨fun n => n < 3, ?_⟩
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator, initConfig]; rfl)
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator]; rfl)
  apply Computes.step _ _ _ (by simp [step, GeneratorExamples.simpleGenerator]; rfl)
  apply Computes.halt
  simp [step, GeneratorExamples.simpleGenerator]

def testCfg0 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  Turing.TM2.init DovetailStack.target []

def testCfg1 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_restoreAll_state
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg0 = some testCfg1 := by
  simp [Turing.TM2.step, Turing.TM2.stepAux, dovetailMachine, check_iterateInstances,
        testCfg0, testCfg1, Turing.TM2.init, default, Inhabited.default]

def testCfg2 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_restoreAll_input
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg1 = some testCfg2 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg1, testCfg2, dovetailMachine,
    check_restoreAll_state, List.head?_nil, Option.isNone_none, cond_true]

def testCfg3 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_restoreAll_workL
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg2 = some testCfg3 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg2, testCfg3, dovetailMachine,
    check_restoreAll_input, List.head?_nil, Option.isNone_none, cond_true]

def testCfg4 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_restoreAll_workR
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg3 = some testCfg4 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg3, testCfg4, dovetailMachine,
    check_restoreAll_workL, List.head?_nil, Option.isNone_none, cond_true]

def testCfg5 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_restoreAll_output
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg4 = some testCfg5 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg4, testCfg5, dovetailMachine,
    check_restoreAll_workR, List.head?_nil, Option.isNone_none, cond_true]

def testCfg6 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.spawn_copyCounter
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg5 = some testCfg6 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg5, testCfg6, dovetailMachine,
    check_restoreAll_output, List.head?_nil, Option.isNone_none, cond_true]

def testCfg7 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.spawn_restoreAndPush
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg6 = some testCfg7 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg6, testCfg7, dovetailMachine,
    spawn_copyCounter, List.head?_nil, Option.isNone_none, cond_true]

def testCfg8 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.stepAll
    var := { transQ      := none
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg7 = some testCfg8 := by
  simp only [Turing.TM2.step, testCfg7, dovetailMachine, spawn_restoreAndPush,
    Turing.TM2.stepAux, List.head?_nil, Option.isNone_none, List.tail_nil,
    Function.update_eq_self, Option.getD_none, ne_eq, reduceCtorEq,
    not_false_eq_true, Function.update_of_ne, cond_true, testCfg8,
    Fin.isValue, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  cases GeneratorExamples.simpleGenerator with
  | mk init blank δ =>
    simp only [Fin.isValue]
    fin_cases init
    simp only [Fin.zero_eta, Fin.isValue]

def testCfg9 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.stepOne
    var := { transQ      := some (0 : Fin 1)
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg8 = some testCfg9 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg8, testCfg9, dovetailMachine,
    stepAll, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg10 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.stepOne_workR
    var := { transQ      := some (0 : Fin 1)
             transW      := none
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := false
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg9 = some testCfg10 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg9, testCfg10, dovetailMachine,
    stepOne, List.head?_nil]

def testCfg11 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.applyTransition
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg10 = some testCfg11 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg10, testCfg11, dovetailMachine,
    stepOne_workR, List.head?_nil, applyDelta, GeneratorExamples.simpleGenerator,
    Bool.false_eq_true, ↓reduceIte, Fin.isValue, List.tail_nil,
    Function.update_eq_self, Bool.cond_self]

def testCfg12 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.workR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg11 = some testCfg12 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg11, testCfg12, dovetailMachine,
    applyTransition, cond_true, Option.getD_some, GeneratorExamples.simpleGenerator,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg13 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment_input
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.workR => [some (0 : Fin 1)]
             | DovetailStack.saveState => [(0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg12 = some testCfg13 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg12, testCfg13, dovetailMachine,
    saveSegment, GeneratorExamples.simpleGenerator, List.head?_cons, List.tail_cons,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg14 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment_workL
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.workR => [some (0 : Fin 1)]
             | DovetailStack.saveState => [(0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg13 = some testCfg14 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg13, testCfg14, dovetailMachine,
    saveSegment_input, List.head?_nil, Option.isNone_none, cond_true]

def testCfg15 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment_workR
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.workR => [some (0 : Fin 1)]
             | DovetailStack.saveState => [(0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg14 = some testCfg15 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg14, testCfg15, dovetailMachine,
    saveSegment_workL, List.head?_nil, Option.isNone_none, cond_true]

def testCfg16 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment_workR
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := some (some (0 : Fin 1))
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.saveState => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg15 = some testCfg16 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg15, testCfg16, dovetailMachine,
    saveSegment_workR, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg17 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.saveSegment_output
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.saveState => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg16 = some testCfg17 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg16, testCfg17, dovetailMachine,
    saveSegment_workR, List.head?_nil, Option.isNone_none, cond_true]

def testCfg18 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.stepAll
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.saveState => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg17 = some testCfg18 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg17, testCfg18, dovetailMachine,
    saveSegment_output, List.head?_nil, Option.isNone_none, cond_true]

def testCfg19 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_state
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.saveState => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg18 = some testCfg19 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg18, testCfg19, dovetailMachine,
    stepAll, List.head?_nil, Option.isNone_none, cond_true]

-- restoreAll_state: peeks saveState (some 0), pops, pushes to state, loops
-- Next: peeks saveState (empty), goes to restoreAll_input
def testCfg20 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_state
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg19 = some testCfg20 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg19, testCfg20, dovetailMachine,
    restoreAll_state, GeneratorExamples.simpleGenerator, List.head?_cons, Option.isNone_some,
    List.tail_cons, cond_false, Option.getD_some,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg21 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_input
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg20 = some testCfg21 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg20, testCfg21, dovetailMachine,
    restoreAll_state, List.head?_nil, Option.isNone_none, cond_true]

-- restoreAll_input: saveInput empty, pushes none to input, goes to restoreAll_workL
def testCfg22 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_workL
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg21 = some testCfg22 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg21, testCfg22, dovetailMachine,
    restoreAll_input, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- restoreAll_workL: saveWorkL empty, pushes none to workL, goes to restoreAll_workR
def testCfg23 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_workR
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.saveWorkR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg22 = some testCfg23 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg22, testCfg23, dovetailMachine,
    restoreAll_workL, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- restoreAll_workR: saveWorkR has [some 0], pops, pushes to workR, loops
-- Then peeks saveWorkR (empty), pushes none to workR, goes to restoreAll_output
def testCfg24 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_workR
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := some (some (0 : Fin 1))
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg23 = some testCfg24 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg23, testCfg24, dovetailMachine,
    restoreAll_workR, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg25 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.restoreAll_output
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg24 = some testCfg25 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg24, testCfg25, dovetailMachine,
    restoreAll_workR, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- restoreAll_output: saveOutput empty, pushes none to output, goes to incrementCounter
def testCfg26 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.incrementCounter
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := none }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg25 = some testCfg26 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg25, testCfg26, dovetailMachine,
    restoreAll_output, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- incrementCounter: sets carry to true, goes to incrementCounter_loop
def testCfg27 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.incrementCounter_loop
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg26 = some testCfg27 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg26, testCfg27, dovetailMachine,
    incrementCounter]

-- incrementCounter_loop: counter empty, carry = true, pushes true, goes to incrementCounter_restore
def testCfg28 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.incrementCounter_restore
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | DovetailStack.counter => [ULift.up true]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg27 = some testCfg28 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg27, testCfg28, dovetailMachine,
    incrementCounter_loop, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- incrementCounter_restore: saveCounter empty, goes to checkAll
def testCfg29 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_iterateInstances
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := none
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | DovetailStack.counter => [ULift.up true]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg28 = some testCfg29 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg28, testCfg29, dovetailMachine,
    incrementCounter_restore, List.head?_nil, Option.isNone_none, cond_true]

-- checkAll: peeks state (some 0), pops, goes to checkOne
def testCfg30 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_testHalting
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := none
             peekWorkL   := none
             peekWorkR   := none
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | DovetailStack.counter => [ULift.up true]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg29 = some testCfg30 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg29, testCfg30, dovetailMachine,
    check_iterateInstances, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- checkOne: peeks input (none separator), peeks workR (none separator),
-- inputBit = false, transW = gen.blank = 0, applyDelta: δ 0 false 0 = none → transHalted = true
-- Halting: pushes state back, goes to checkOutput
def testCfg31 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.check_compareOutput
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := some none
             peekWorkL   := none
             peekWorkR   := some none
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | DovetailStack.counter => [ULift.up true]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg30 = some testCfg31 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg30, testCfg31, dovetailMachine,
    check_testHalting, GeneratorExamples.simpleGenerator, applyDelta, List.head?_cons,
    Bool.false_eq_true, ↓reduceIte, cond_true, Option.getD_some,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg32 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := none
    var := { transQ      := some (0 : Fin 1)
             transW      := some (0 : Fin 1)
             transIDir   := InputTapeDirection.N
             transWDir   := WorkTapeDirection.N
             transOut    := none
             transHalted := true
             inputBit    := ULift.up false
             peekQ       := some (0 : Fin 1)
             peekBit     := none
             peekInput   := some none
             peekWorkL   := none
             peekWorkR   := some none
             peekOut     := some none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state => [(0 : Fin 1)]
             | DovetailStack.input => [none]
             | DovetailStack.workL => [none]
             | DovetailStack.workR => [none, some (0 : Fin 1)]
             | DovetailStack.output => [none]
             | DovetailStack.counter => [ULift.up true]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg31 = some testCfg32 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg31, testCfg32, dovetailMachine,
    check_compareOutput, List.head?_nil, Option.isNone_none, cond_true, List.head?_cons]

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg32 = none := by
  simp [Turing.TM2.step, testCfg32]

instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.target)    := inferInstanceAs (Repr (Fin 2))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.counter)   := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.input)     := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.state)     := inferInstanceAs (Repr (Fin 1))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.workL)     := inferInstanceAs (Repr (Option (Fin 1)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.workR)     := inferInstanceAs (Repr (Option (Fin 1)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.output)    := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveTarget)  := inferInstanceAs (Repr (Fin 2))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveCounter) := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveInput)   := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveState)   := inferInstanceAs (Repr (Fin 1))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveWorkL)   := inferInstanceAs (Repr (Option (Fin 1)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveWorkR)   := inferInstanceAs (Repr (Option (Fin 1)))
instance : Repr (stackAlphabet (Fin 1) (Fin 2) (Fin 1) DovetailStack.saveOutput)  := inferInstanceAs (Repr (Option (Fin 2)))

def reprCfg (cfg : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1))) : String :=
  let l := repr cfg.l
  let var := repr cfg.var
  let target    := repr (cfg.stk DovetailStack.target)
  let counter   := repr (cfg.stk DovetailStack.counter)
  let input     := repr (cfg.stk DovetailStack.input)
  let state     := repr (cfg.stk DovetailStack.state)
  let workL     := repr (cfg.stk DovetailStack.workL)
  let workR     := repr (cfg.stk DovetailStack.workR)
  let output    := repr (cfg.stk DovetailStack.output)
  let saveTgt   := repr (cfg.stk DovetailStack.saveTarget)
  let saveCtr   := repr (cfg.stk DovetailStack.saveCounter)
  let saveInp   := repr (cfg.stk DovetailStack.saveInput)
  let saveSt    := repr (cfg.stk DovetailStack.saveState)
  let saveWL    := repr (cfg.stk DovetailStack.saveWorkL)
  let saveWR    := repr (cfg.stk DovetailStack.saveWorkR)
  let saveOut   := repr (cfg.stk DovetailStack.saveOutput)
  s!"label: {l}\nvar: {var}\ntarget: {target}\ncounter: {counter}\ninput: {input}\nstate: {state}\nworkL: {workL}\nworkR: {workR}\noutput: {output}\nsaveTarget: {saveTgt}\nsaveCounter: {saveCtr}\nsaveInput: {saveInp}\nsaveState: {saveSt}\nsaveWorkL: {saveWL}\nsaveWorkR: {saveWR}\nsaveOutput: {saveOut}"

def runTraceStr (n : ℕ) : String :=
  let rec loop
      (fuel : ℕ)
      (step : ℕ)
      (cfg : Option
        (Turing.TM2.Cfg
          (stackAlphabet (Fin 1) (Fin 2) (Fin 1))
          DovetailLabel
          (DovetailSigma (Fin 1) (Fin 2) (Fin 1))))
      (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match cfg with
      | none =>
        acc ++ s!"=== Halted at step {step} ===\n"
      | some c =>
        let acc :=
          acc
          ++ s!"=== Step {step} ===\n"
          ++ reprCfg c ++ "\n"
        let cfg' := cfg.bind
            (Turing.TM2.step
              (dovetailMachine GeneratorExamples.simpleGenerator))
        loop fuel (step + 1) cfg' acc
  loop n 0
    (some (dovetailInit (Γw := Fin 1) (Γo := Fin 2) (Q := Fin 1) [1]))
    ""

#guard (runTraceStr.{0, 0} 113).endsWith "=== Halted at step 112 ===\n"

end SimpleGenerator

namespace TallyGenerator

instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.target)    := inferInstanceAs (Repr (Fin 2))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.counter)   := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.input)     := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.state)     := inferInstanceAs (Repr (Fin 3))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.workL)     := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.workR)     := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.output)    := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveTarget)  := inferInstanceAs (Repr (Fin 2))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveCounter) := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveInput)   := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveState)   := inferInstanceAs (Repr (Fin 3))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveWorkL)   := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveWorkR)   := inferInstanceAs (Repr (Option (Fin 2)))
instance : Repr (stackAlphabet (Fin 2) (Fin 2) (Fin 3) DovetailStack.saveOutput)  := inferInstanceAs (Repr (Option (Fin 2)))

def reprCfg (cfg : Turing.TM2.Cfg (stackAlphabet (Fin 2) (Fin 2) (Fin 3)) DovetailLabel (DovetailSigma (Fin 2) (Fin 2) (Fin 3))) : String :=
  let l := repr cfg.l
  let var := repr cfg.var
  let target    := repr (cfg.stk DovetailStack.target)
  let counter   := repr (cfg.stk DovetailStack.counter)
  let input     := repr (cfg.stk DovetailStack.input)
  let state     := repr (cfg.stk DovetailStack.state)
  let workL     := repr (cfg.stk DovetailStack.workL)
  let workR     := repr (cfg.stk DovetailStack.workR)
  let output    := repr (cfg.stk DovetailStack.output)
  let saveTgt   := repr (cfg.stk DovetailStack.saveTarget)
  let saveCtr   := repr (cfg.stk DovetailStack.saveCounter)
  let saveInp   := repr (cfg.stk DovetailStack.saveInput)
  let saveSt    := repr (cfg.stk DovetailStack.saveState)
  let saveWL    := repr (cfg.stk DovetailStack.saveWorkL)
  let saveWR    := repr (cfg.stk DovetailStack.saveWorkR)
  let saveOut   := repr (cfg.stk DovetailStack.saveOutput)
  s!"label: {l}\nvar: {var}\ntarget: {target}\ncounter: {counter}\ninput: {input}\nstate: {state}\nworkL: {workL}\nworkR: {workR}\noutput: {output}\nsaveTarget: {saveTgt}\nsaveCounter: {saveCtr}\nsaveInput: {saveInp}\nsaveState: {saveSt}\nsaveWorkL: {saveWL}\nsaveWorkR: {saveWR}\nsaveOutput: {saveOut}"

def runTrace (n : ℕ) (target : List (Fin 2)) : IO Unit := do
  let mut cfg : Option (Turing.TM2.Cfg _ DovetailLabel _) :=
    some (dovetailInit (Γw := Fin 2) (Γo := Fin 2) (Q := Fin 3) target)
  for i in List.range n do
    match cfg with
    | none =>
      IO.println s!"=== Halted at step {i} ==="
      return
    | some c =>
      IO.println s!"=== Step {i} ==="
      IO.println (reprCfg c)
      cfg := cfg.bind (Turing.TM2.step (dovetailMachine GeneratorExamples.tallyGenerator))

def runTraceStr (n : ℕ) : String :=
  let rec loop
      (fuel : ℕ)
      (step : ℕ)
      (cfg : Option
        (Turing.TM2.Cfg
          (stackAlphabet (Fin 2) (Fin 2) (Fin 3))
          DovetailLabel
          (DovetailSigma (Fin 2) (Fin 2) (Fin 3))))
      (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match cfg with
      | none =>
        acc ++ s!"=== Halted at step {step} ===\n"
      | some c =>
        let acc :=
          acc
          ++ s!"=== Step {step} ===\n"
          ++ reprCfg c ++ "\n"
        let cfg' : Option (Turing.TM2.Cfg
            (stackAlphabet (Fin 2) (Fin 2) (Fin 3))
            DovetailLabel
            (DovetailSigma (Fin 2) (Fin 2) (Fin 3))) :=
          cfg.bind
            (Turing.TM2.step
              (dovetailMachine GeneratorExamples.tallyGenerator))
        loop fuel (step + 1) cfg' acc
  loop n 0
    (some (dovetailInit (Γw := Fin 2) (Γo := Fin 2) (Q := Fin 3) [1, 1]))
    ""

--#eval IO.println ((runTraceStr.{0, 0} 2000).takeEnd 100)
--#guard (runTraceStr.{0, 0} 1371).endsWith "=== Halted at step 1370 ===\n"

end TallyGenerator

namespace MoveRightLeftGenerator

instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.target)    := inferInstanceAs (Repr (Fin 10))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.counter)   := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.input)     := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.state)     := inferInstanceAs (Repr (Fin 10))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.workL)     := inferInstanceAs (Repr (Option (Fin 10)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.workR)     := inferInstanceAs (Repr (Option (Fin 10)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.output)    := inferInstanceAs (Repr (Option (Fin 10)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveTarget)  := inferInstanceAs (Repr (Fin 10))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveCounter) := inferInstanceAs (Repr (ULift Bool))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveInput)   := inferInstanceAs (Repr (Option (ULift Bool)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveState)   := inferInstanceAs (Repr (Fin 10))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveWorkL)   := inferInstanceAs (Repr (Option (Fin 10)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveWorkR)   := inferInstanceAs (Repr (Option (Fin 10)))
instance : Repr (stackAlphabet (Fin 10) (Fin 10) (Fin 10) DovetailStack.saveOutput)  := inferInstanceAs (Repr (Option (Fin 10)))

def reprCfg (cfg : Turing.TM2.Cfg (stackAlphabet (Fin 10) (Fin 10) (Fin 10)) DovetailLabel (DovetailSigma (Fin 10) (Fin 10) (Fin 10))) : String :=
  let l := repr cfg.l
  let var := repr cfg.var
  let target    := repr (cfg.stk DovetailStack.target)
  let counter   := repr (cfg.stk DovetailStack.counter)
  let input     := repr (cfg.stk DovetailStack.input)
  let state     := repr (cfg.stk DovetailStack.state)
  let workL     := repr (cfg.stk DovetailStack.workL)
  let workR     := repr (cfg.stk DovetailStack.workR)
  let output    := repr (cfg.stk DovetailStack.output)
  let saveTgt   := repr (cfg.stk DovetailStack.saveTarget)
  let saveCtr   := repr (cfg.stk DovetailStack.saveCounter)
  let saveInp   := repr (cfg.stk DovetailStack.saveInput)
  let saveSt    := repr (cfg.stk DovetailStack.saveState)
  let saveWL    := repr (cfg.stk DovetailStack.saveWorkL)
  let saveWR    := repr (cfg.stk DovetailStack.saveWorkR)
  let saveOut   := repr (cfg.stk DovetailStack.saveOutput)
  s!"label: {l}\nvar: {var}\ntarget: {target}\ncounter: {counter}\ninput: {input}\nstate: {state}\nworkL: {workL}\nworkR: {workR}\noutput: {output}\nsaveTarget: {saveTgt}\nsaveCounter: {saveCtr}\nsaveInput: {saveInp}\nsaveState: {saveSt}\nsaveWorkL: {saveWL}\nsaveWorkR: {saveWR}\nsaveOutput: {saveOut}"
  --s!"label: {l}\ntarget: {target}\nstate: {state}\ninput: {input}\nworkR: {workR}\noutput: {output}\nsaveTarget: {saveTgt}\nsaveOutput: {saveOut}"

def runTraceStr (n : ℕ) (gen : Generator (Fin 10) (Fin 10) (Fin 10)) : String :=
  let rec loop
      (fuel : ℕ)
      (step : ℕ)
      (cfg : Option
        (Turing.TM2.Cfg
          (stackAlphabet (Fin 10) (Fin 10) (Fin 10))
          DovetailLabel
          (DovetailSigma (Fin 10) (Fin 10) (Fin 10))))
      (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
      match cfg with
      | none =>
        acc ++ s!"=== Halted at step {step} ===\n"
      | some c =>
        let isCheckpoint :=
          (match c.l with
          | some DovetailLabel.check_iterateInstances => true
          | some DovetailLabel.check_testHalting => true
          | some DovetailLabel.check_compareOutput => true
          | some DovetailLabel.check_compareOutput_restoreTarget => true
          | some DovetailLabel.check_compareOutput_restoreOutput => true
          | some DovetailLabel.check_saveInstance_state => true
          | none => true
          | _ => false)
        -- let isCheckpoint :=
        --   (match c.l with
        --   | some DovetailLabel.pushNewConfig_copy_counter =>
        --       (c.stk DovetailStack.saveCounter).length == 0
        --   | none => true
        --   | _ => false)
        let acc := if isCheckpoint then
          acc
          ++ s!"=== Step {step} ===\n"
          ++ reprCfg c ++ "\n"
        else acc
        let cfg' : Option (Turing.TM2.Cfg
            (stackAlphabet (Fin 10) (Fin 10) (Fin 10))
            DovetailLabel
            (DovetailSigma (Fin 10) (Fin 10) (Fin 10))) :=
          cfg.bind
            (Turing.TM2.step
              (dovetailMachine gen))
        loop fuel (step + 1) cfg' acc
  loop n 0
    (some (dovetailInit (Γw := Fin 10) (Γo := Fin 10) (Q := Fin 10) [0, 1, 2, 3, 4, 5, 6, 7, 8]))
    ""

#eval IO.println (runTraceStr.{0, 0} 1371 GeneratorExamples.moveRightGenerator)
--#guard (runTraceStr.{0, 0} 1371 GeneratorExamples.moveRightGenerator).endsWith "=== Halted at step 1370 ===\n"

end MoveRightLeftGenerator

set_option linter.style.longLine true
set_option linter.hashCommand true
end DovetailingExamples

end RandomisedGeneration
