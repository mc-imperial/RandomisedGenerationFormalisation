import RandomisedGeneration.GeneratorExamples
import RandomisedGeneration.GreedyEnum.GreedyEnumTM2

namespace RandomisedGeneration

namespace GreedyEnumExamples
set_option linter.style.longLine false
set_option linter.hashCommand false

deriving instance Repr for GreedyEnum.GreedyEnumStack
deriving instance Repr for GreedyEnum.GreedyEnumLabel
deriving instance Repr for InputTapeDirection
deriving instance Repr for WorkTapeDirection
deriving instance Repr for GreedyEnum.GreedyEnumSigma

open GreedyEnum in
def stripPrefix (s : String) : String :=
  (s.splitOn ".").getLast!

open GreedyEnum in
def reprCfg
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.target)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.counter)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.input)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workL)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workR)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.output)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveCounter)]
    (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q)) : String :=
  let showStack (name : String) (s : String) : Option String :=
    if s == "[]" then none else some s!"  {name}: {s}"
  let r := fun {α} [Repr α] (x : α) => toString (repr x)
  let lines : List String := List.filterMap id [
    some s!"  label: {stripPrefix (r cfg.l)}",
    showStack "target     " (r (cfg.stk GreedyEnumStack.target)),
    showStack "counter    " (r (cfg.stk GreedyEnumStack.counter)),
    showStack "input      " (r (cfg.stk GreedyEnumStack.input)),
    showStack "workL      " (r (cfg.stk GreedyEnumStack.workL)),
    showStack "workR      " (r (cfg.stk GreedyEnumStack.workR)),
    showStack "output     " (r (cfg.stk GreedyEnumStack.output)),
    showStack "saveTarget " (r (cfg.stk GreedyEnumStack.saveTarget)),
    showStack "saveCounter" (r (cfg.stk GreedyEnumStack.saveCounter))
  ]
  "\n".intercalate lines

open GreedyEnum in
def runTraceStr
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.target)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.counter)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.input)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workL)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workR)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.output)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveCounter)]
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (n : ℕ) : String :=
  Id.run do
    let mut cfg := greedyEnumInit (Γw := Γw) (Γo := Γo) (Q := Q) target
    let mut acc := ""
    for step in List.range n do
      acc := acc ++ s!"=== Step {step} ===\n" ++ reprCfg cfg ++ "\n"
      match Turing.TM2.step (greedyEnumMachine gen) cfg with
      | none =>
        acc := acc ++ s!"=== Halted after step {step} ===\n"
        return acc
      | some c' =>
        cfg := c'
    return acc

open GreedyEnum in
def runTraceStrRoundStarts
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.target)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.counter)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.input)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workL)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.workR)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.output)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveTarget)]
    [Repr (stackAlphabet Γw Γo Q GreedyEnumStack.saveCounter)]
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (n : ℕ) : String :=
  let isRoundStart (cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) GreedyEnumLabel (GreedyEnumSigma Γw Γo Q)) : Bool :=
    cfg.l == some GreedyEnumLabel.copyCounter
  Id.run do
    let mut cfg := greedyEnumInit (Γw := Γw) (Γo := Γo) (Q := Q) target
    let mut acc := ""
    for step in List.range n do
      if isRoundStart cfg then
        acc := acc ++ s!"=== Step {step} ===\n" ++ reprCfg cfg ++ "\n"
      match Turing.TM2.step (greedyEnumMachine gen) cfg with
      | none =>
        acc := acc ++ s!"=== Halted after step {step} ===\n"
        return acc
      | some c' =>
        cfg := c'
    return acc

open GreedyEnum in
instance instReprStackAlphabet
    {Γw Γo Q : Type}
    [FinEnum Γw] [Inhabited Γw]
    [FinEnum Γo] [Inhabited Γo]
    [FinEnum Q] [Inhabited Q]
    [Repr Γo] [Repr Γw] [Repr Q]
    (s : GreedyEnumStack) : Repr (stackAlphabet Γw Γo Q s) :=
  match s with
  | .target      => inferInstanceAs (Repr Γo)
  | .counter     => inferInstanceAs (Repr (ULift Bool))
  | .input       => inferInstanceAs (Repr (ULift Bool))
  | .workL       => inferInstanceAs (Repr Γw)
  | .workR       => inferInstanceAs (Repr Γw)
  | .output      => inferInstanceAs (Repr Γo)
  | .saveTarget  => inferInstanceAs (Repr Γo)
  | .saveCounter => inferInstanceAs (Repr (ULift Bool))

-- ══════════════════════════════════════════════════════════════════════════
-- Test generators
-- ══════════════════════════════════════════════════════════════════════════

/-- Halts immediately on any input, producing empty output.
    Should match target [] on the very first bitstring (counter = []). -/
def immediateHaltGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q _b _w => none

/-- Reads one bit; halts. If bit = true, outputs 1; if false, outputs nothing.
    Greedy: always advances input head.
    On bitstring [true] (counter = [true], i.e. idx=1, len=1),
    outputs [1] and halts. -/
def readOneHaltGenerator : Generator (Fin 1) (Fin 2) (Fin 2) where
  init  := 0
  blank := 0
  δ := fun q b _w =>
    match q with
    | 0 => if b then some (1, 0, some 1, InputTapeDirection.R, WorkTapeDirection.N)
            else some (1, 0, none, InputTapeDirection.R, WorkTapeDirection.N)
    | 1 => none

/-- Never halts: always transitions, advancing input head.
    Tests that the machine correctly times out and advances. -/
def nonHaltingGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q _b _w =>
    some (0, 0, some 1, InputTapeDirection.R, WorkTapeDirection.N)

/-- Reads bits until it sees true, outputting 1 for each false bit read.
    On true, halts. Greedy: always advances.
    On bitstring [false, true] (idx=2, len=2): reads false→output 1,
    reads true→halt. Output = [1]. -/
def countFalsesGenerator : Generator (Fin 1) (Fin 2) (Fin 1) where
  init  := 0
  blank := 0
  δ := fun _q b _w =>
    if b then none
    else some (0, 0, some 1, InputTapeDirection.R, WorkTapeDirection.N)

-- ══════════════════════════════════════════════════════════════════════════
-- Trace commands (uncomment to run)
-- ══════════════════════════════════════════════════════════════════════════

-- Empty target, immediate halt generator: should halt very quickly
--#eval IO.println (runTraceStr immediateHaltGenerator ([] : List (Fin 2)) 50)

-- Target [1], readOneHalt: should find match on bitstring [true]
--#eval IO.println (runTraceStr readOneHaltGenerator [1] 200)

-- Non-halting generator: should loop through bitstrings without ever halting
--#eval IO.println (runTraceStrRoundStarts nonHaltingGenerator ([] : List (Fin 2)) 500)

-- Count falses, target [1]: match on bitstring with exactly one false then true
--#eval IO.println (runTraceStrRoundStarts countFalsesGenerator [1] 500)

-- Detailed trace of count falses
--#eval IO.println (runTraceStr countFalsesGenerator [1] 300)

end GreedyEnumExamples

end RandomisedGeneration
