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

def stripPrefix (s : String) : String :=
  (s.splitOn ".").getLast!

def reprCfg
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.target)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.counter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.input)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.state)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.output)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveCounter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveInput)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveState)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveOutput)]
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q)) : String :=
  let showStack (name : String) (s : String) : Option String :=
    if s == "[]" then none else some s!"  {name}: {s}"
  let r := fun {α} [Repr α] (x : α) => toString (repr x)
  let lines : List String := List.filterMap id [
    some s!"  label: {stripPrefix (r cfg.l)}",
    showStack "target     " (r (cfg.stk DovetailStack.target)),
    showStack "counter    " (r (cfg.stk DovetailStack.counter)),
    showStack "input      " (r (cfg.stk DovetailStack.input)),
    showStack "state      " (r (cfg.stk DovetailStack.state)),
    showStack "workL      " (r (cfg.stk DovetailStack.workL)),
    showStack "workR      " (r (cfg.stk DovetailStack.workR)),
    showStack "output     " (r (cfg.stk DovetailStack.output)),
    showStack "saveTarget " (r (cfg.stk DovetailStack.saveTarget)),
    showStack "saveCounter" (r (cfg.stk DovetailStack.saveCounter)),
    showStack "saveInput  " (r (cfg.stk DovetailStack.saveInput)),
    showStack "saveState  " (r (cfg.stk DovetailStack.saveState)),
    showStack "saveWorkL  " (r (cfg.stk DovetailStack.saveWorkL)),
    showStack "saveWorkR  " (r (cfg.stk DovetailStack.saveWorkR)),
    showStack "saveOutput " (r (cfg.stk DovetailStack.saveOutput))
  ]
  "\n".intercalate lines

def runTraceStr
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.target)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.counter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.input)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.state)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.output)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveCounter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveInput)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveState)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveOutput)]
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (n : ℕ) : String :=
  Id.run do
    let mut cfg := dovetailInit (Γw := Γw) (Γo := Γo) (Q := Q) target
    let mut acc := ""
    for step in List.range n do
      acc := acc ++ s!"=== Step {step} ===\n" ++ reprCfg cfg ++ "\n"
      match Turing.TM2.step (dovetailMachine gen) cfg with
      | none =>
        acc := acc ++ s!"=== Halted after step {step} ===\n"
        return acc
      | some c' =>
        cfg := c'
    return acc

def runTraceStrRoundStarts
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.target)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.counter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.input)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.state)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.workR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.output)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveCounter)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveInput)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveState)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkL)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveWorkR)]
    [Repr (stackAlphabet Γw Γo Q DovetailStack.saveOutput)]
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (n : ℕ) : String :=
  let isRoundStart (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q)) : Bool :=
    cfg.l == some DovetailLabel.check_iterateInstances &&
    (cfg.stk DovetailStack.saveState).length == 0
  Id.run do
    let mut cfg := dovetailInit (Γw := Γw) (Γo := Γo) (Q := Q) target
    let mut acc := ""
    for step in List.range n do
      if isRoundStart cfg then
        acc := acc ++ s!"=== Step {step} ===\n" ++ reprCfg cfg ++ "\n"
      match Turing.TM2.step (dovetailMachine gen) cfg with
      | none =>
        acc := acc ++ s!"=== Halted after step {step} ===\n"
        return acc
      | some c' =>
        cfg := c'
    return acc

instance instReprStackAlphabet
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr Γo] [Repr Γw] [Repr Q]
    (s : DovetailStack) : Repr (stackAlphabet Γw Γo Q s) :=
  match s with
  | .target      => inferInstanceAs (Repr Γo)
  | .counter     => inferInstanceAs (Repr (ULift Bool))
  | .input       => inferInstanceAs (Repr (Option (ULift Bool)))
  | .state       => inferInstanceAs (Repr Q)
  | .workL       => inferInstanceAs (Repr (Option Γw))
  | .workR       => inferInstanceAs (Repr (Option Γw))
  | .output      => inferInstanceAs (Repr (Option Γo))
  | .saveTarget  => inferInstanceAs (Repr Γo)
  | .saveCounter => inferInstanceAs (Repr (ULift Bool))
  | .saveInput   => inferInstanceAs (Repr (Option (ULift Bool)))
  | .saveState   => inferInstanceAs (Repr Q)
  | .saveWorkL   => inferInstanceAs (Repr (Option Γw))
  | .saveWorkR   => inferInstanceAs (Repr (Option Γw))
  | .saveOutput  => inferInstanceAs (Repr (Option Γo))

--#eval IO.println (runTraceStr GeneratorExamples.simpleGenerator [1] 200)

def nonHaltingGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q _b _w =>
    some (0, 0, some 1, InputTapeDirection.N, WorkTapeDirection.N)

--#eval IO.println (runTraceStr nonHaltingGenerator [0] 300)

--#eval IO.println (runTraceStrRoundStarts nonHaltingGenerator [0] 1000)

--#eval IO.println (runTraceStr GeneratorExamples.tallyGenerator [1, 1] 500)

--#eval IO.println (runTraceStrRoundStarts GeneratorExamples.moveRightGenerator [1, 1] 500)

--#eval IO.println (runTraceStrRoundStarts GeneratorExamples.moveLeftGenerator [1, 1] 500)

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
  { l := some DovetailLabel.step_iterateInstances
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
  { l := some DovetailLabel.step_peekInput
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
    step_iterateInstances, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg10 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_peekWorkR
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
    step_peekInput, List.head?_nil]

def testCfg11 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_applyTransition
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
    step_peekWorkR, List.head?_nil, applyDelta, GeneratorExamples.simpleGenerator,
    Bool.false_eq_true, ↓reduceIte, Fin.isValue, List.tail_nil,
    Function.update_eq_self, Bool.cond_self]

def testCfg12 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_state
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
    step_applyTransition, cond_true, Option.getD_some, GeneratorExamples.simpleGenerator,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg13 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_input
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
    step_saveInstance_state, GeneratorExamples.simpleGenerator, List.head?_cons, List.tail_cons,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg14 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_workL
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
    step_saveInstance_input, List.head?_nil, Option.isNone_none, cond_true]

def testCfg15 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_workR
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
    step_saveInstance_workL, List.head?_nil, Option.isNone_none, cond_true]

def testCfg16 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_workR
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
    step_saveInstance_workR, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg17 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_saveInstance_output
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
    step_saveInstance_workR, List.head?_nil, Option.isNone_none, cond_true]

def testCfg18 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_iterateInstances
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
    step_saveInstance_output, List.head?_nil, Option.isNone_none, cond_true]

def testCfg19 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_state
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
    step_iterateInstances, List.head?_nil, Option.isNone_none, cond_true]

-- step_restoreAll_state: peeks saveState (some 0), pops, pushes to state, loops
-- Next: peeks saveState (empty), goes to step_restoreAll_input
def testCfg20 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_state
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
    step_restoreAll_state, GeneratorExamples.simpleGenerator, List.head?_cons, Option.isNone_some,
    List.tail_cons, cond_false, Option.getD_some,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg21 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_input
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
    step_restoreAll_state, List.head?_nil, Option.isNone_none, cond_true]

-- step_restoreAll_input: saveInput empty, pushes none to input, goes to step_restoreAll_workL
def testCfg22 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_workL
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
    step_restoreAll_input, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- step_restoreAll_workL: saveWorkL empty, pushes none to workL, goes to step_restoreAll_workR
def testCfg23 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_workR
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
    step_restoreAll_workL, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- step_restoreAll_workR: saveWorkR has [some 0], pops, pushes to workR, loops
-- Then peeks saveWorkR (empty), pushes none to workR, goes to step_restoreAll_output
def testCfg24 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_workR
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
    step_restoreAll_workR, List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    Option.getD_some, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg25 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.step_restoreAll_output
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
    step_restoreAll_workR, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- step_restoreAll_output: saveOutput empty, pushes none to output, goes to counter_increment
def testCfg26 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.counter_increment
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
    step_restoreAll_output, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- counter_increment: sets carry to true, goes to counter_increment_loop
def testCfg27 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.counter_increment_loop
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
    counter_increment]

-- counter_increment_loop: counter empty, carry = true, pushes true, goes to counter_increment_restore
def testCfg28 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.counter_increment_restore
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
    counter_increment_loop, List.head?_nil, Option.isNone_none, cond_true,
    Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

-- counter_increment_restore: saveCounter empty, goes to checkAll
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
    counter_increment_restore, List.head?_nil, Option.isNone_none, cond_true]

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
             | DovetailStack.state      => [(0 : Fin 1)]
             | DovetailStack.input      => [none]
             | DovetailStack.workL      => [none]
             | DovetailStack.workR      => [none, some (0 : Fin 1)]
             | DovetailStack.output     => []
             | DovetailStack.counter    => [ULift.up true]
             | DovetailStack.saveOutput => [none]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg30 = some testCfg31 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg30, testCfg31, dovetailMachine,
    check_testHalting, applyDelta, GeneratorExamples.simpleGenerator,
    List.head?_cons, Bool.false_eq_true, ite_false, Option.getD_some, Bool.cond_true,
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
             peekOut     := none
             peekTarget  := none
             carry       := some (ULift.up true) }
    stk := fun k => match k with
             | DovetailStack.state      => [(0 : Fin 1)]
             | DovetailStack.input      => [none]
             | DovetailStack.workL      => [none]
             | DovetailStack.workR      => [none, some (0 : Fin 1)]
             | DovetailStack.output     => []
             | DovetailStack.counter    => [ULift.up true]
             | DovetailStack.saveOutput => [none]
             | _ => [] }

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg31 = some testCfg32 := by
  simp only [Turing.TM2.step, Turing.TM2.stepAux, testCfg31, testCfg32, dovetailMachine,
    check_compareOutput, List.head?_nil, Option.isNone_none, cond_true]

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg32 = none := by
  simp [Turing.TM2.step, testCfg32]

end SimpleGenerator

set_option linter.style.longLine true
set_option linter.hashCommand true
end DovetailingExamples

end RandomisedGeneration
