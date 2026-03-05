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
  { l := some DovetailLabel.pushNewConfig_restore_counter
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
  simp [Turing.TM2.step, Turing.TM2.stepAux, dovetailMachine, pushNewConfig_copy_counter,
        testCfg0, testCfg1, Turing.TM2.init, default, Inhabited.default]

def testCfg2 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg1 = some testCfg2 := by
  simp only [Turing.TM2.step, testCfg1, dovetailMachine, pushNewConfig_restore_counter, Turing.TM2.stepAux,
    List.head?_nil, Option.isNone_none, List.tail_nil, Function.update_eq_self, Option.getD_none, ne_eq, reduceCtorEq,
    not_false_eq_true, Function.update_of_ne, cond_true, testCfg2, Fin.isValue, Option.some.injEq,
    Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  cases GeneratorExamples.simpleGenerator with
  | mk init blank δ =>
    simp only [Fin.isValue]
    fin_cases init
    simp only [Fin.zero_eta, Fin.isValue]

def testCfg3 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg2 = some testCfg3 := by
  simp only [Turing.TM2.step, testCfg2, dovetailMachine, stepAll, Turing.TM2.stepAux,
    List.head?_cons, Option.isNone_some, List.tail_cons, cond_false,
    testCfg3, Option.some.injEq, Turing.TM2.Cfg.mk.injEq, true_and]
  funext k
  cases k <;> simp [Function.update]

def testCfg4 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg3 = some testCfg4 := by
  simp only [Turing.TM2.step, testCfg3, dovetailMachine, stepOne, Turing.TM2.stepAux,
    List.head?_nil, testCfg4]

def testCfg5 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg4 = some testCfg5 := by
  simp only [Turing.TM2.step, testCfg4, dovetailMachine, stepOne_workR, Turing.TM2.stepAux,
    List.head?_nil, applyDelta, GeneratorExamples.simpleGenerator, testCfg5,
    Bool.false_eq_true, ↓reduceIte, Fin.isValue, List.tail_nil,
    Function.update_eq_self, Bool.cond_self]

def testCfg6 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
  { l := some DovetailLabel.checkOutput
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg5 = some testCfg6 := by
  simp only [Turing.TM2.step, testCfg5, dovetailMachine, applyTransition, Turing.TM2.stepAux,
    testCfg6, cond_true, Option.getD_some, GeneratorExamples.simpleGenerator]
  congr 1
  congr 1
  funext k
  cases k <;> simp [Function.update]

def testCfg7 : Turing.TM2.Cfg (stackAlphabet (Fin 1) (Fin 2) (Fin 1)) DovetailLabel (DovetailSigma (Fin 1) (Fin 2) (Fin 1)) :=
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

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg6 = some testCfg7 := by
  simp only [Turing.TM2.step, testCfg6, dovetailMachine, checkOutput, Turing.TM2.stepAux,
    List.head?_nil, Option.isNone_none, cond_true, testCfg7]

example : Turing.TM2.step (dovetailMachine GeneratorExamples.simpleGenerator) testCfg7 = none := by
  simp [Turing.TM2.step, testCfg7]

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

#guard (runTraceStr.{0, 0} 108).endsWith "=== Halted at step 107 ===\n"

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

#guard (runTraceStr.{0, 0} 1371).endsWith "=== Halted at step 1370 ===\n"

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
          | some DovetailLabel.pushNewConfig_copy_counter =>
              (c.stk DovetailStack.saveCounter).length == 0
          | none => true
          | _ => false)
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
