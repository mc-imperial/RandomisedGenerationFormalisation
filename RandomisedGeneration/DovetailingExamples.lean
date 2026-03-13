import RandomisedGeneration.GeneratorExamples
import RandomisedGeneration.Dovetailing.DovetailingTM2

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
    cfg.l == some DovetailLabel.check_stripSeparators
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

def bugExposingGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q b _w =>
    if b then
      none  -- halt on true
    else
      some (0, 0, some 1, InputTapeDirection.R, WorkTapeDirection.N)
      -- on false: output a 1, advance input, continue

--#eval IO.println (runTraceStr bugExposingGenerator [] 500)

--#eval IO.println (runTraceStrRoundStarts bugExposingGenerator [3, 2, 1, 0] 500)

end DovetailingExamples

end RandomisedGeneration
