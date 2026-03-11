import Mathlib
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Dovetailing.AbstractMachine
import RandomisedGeneration.Dovetailing.DovetailingTM2

namespace RandomisedGeneration

universe u

section Dovetailing
set_option linter.unusedSectionVars false

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-- The config of instance i after round rounds. -/
def instanceConfig
    (gen : Generator Γw Γo Q)
    (i : ℕ) (round : ℕ) : GenConfig Γw Γo Q :=
  stepNHalt gen (initConfig gen i.testBit) (round - i)

def workRMatches
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (seg : List (Option Γw))
    (bound : ℕ) : Prop :=
  ∀ j : ℕ, j < bound →
    if h : j < seg.length then
      seg[j] = some (cfg.work (cfg.workIndex + 1 + ↑j))
    else
      cfg.work (cfg.workIndex + 1 + ↑j) = gen.blank

def workLMatches
    (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q)
    (seg : List (Option Γw))
    (bound : ℕ) : Prop :=
  ∀ j : ℕ, j < bound →
    if h : j < seg.length then
      seg[j] = some (cfg.work (cfg.workIndex - 1 - ↑j))
    else
      cfg.work (cfg.workIndex - 1 - ↑j) = gen.blank

def segWorkR (cfg : GenConfig Γw Γo Q) (bound : ℕ) : List (Option Γw) :=
  (List.range bound).map (fun j => some (cfg.work (cfg.workIndex + 1 + ↑j)))

def segWorkL (cfg : GenConfig Γw Γo Q) (bound : ℕ) : List (Option Γw) :=
  (List.range bound).map (fun j => some (cfg.work (cfg.workIndex - 1 - ↑j)))

lemma workRMatches_segWorkR (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q) (bound : ℕ) :
    workRMatches gen cfg (segWorkR cfg bound) bound := by
  intro j hj
  simp [segWorkR, List.length_map, List.length_range]
  omega

lemma workLMatches_segWorkL (gen : Generator Γw Γo Q)
    (cfg : GenConfig Γw Γo Q) (bound : ℕ) :
    workLMatches gen cfg (segWorkL cfg bound) bound := by
  intro j hj
  simp [segWorkL, List.length_map, List.length_range]
  omega

/-- Quiescent invariant: the TM2 stacks correctly represent the state of
    the abstract dovetail machine at the start of a round.

    The quiescent point is at check_stripSeparators, which is the entry
    point of the main loop (reached from counter_increment_restore, or
    directly on round 0).

    Parameterised by:
    • gen: the generator being dovetailed
    • target: the word on the target stack (set at initialisation, never modified)
    • round: the number of completed rounds (= number of spawned instances)
    • tm2cfg: the TM2 configuration

    At round r, there are r instances. Instance i (0-indexed, 0 = oldest)
    has been stepped (r - i) times. Its abstract state is given by
    instanceConfig gen i r = stepNHalt gen (initConfig gen i.testBit) (r - i).

    The stacks encode all r instances' data with none separators before
    each segment: [none, stuff_newest, none, stuff, ..., none, stuff_oldest].
    Newest instance data is on top of each stack. -/
structure QuiescentInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop where
  label_eq : tm2cfg.l = some DovetailLabel.check_stripSeparators
  counter : tm2cfg.stk DovetailStack.counter = (Nat.bits round).map ULift.up
  input : tm2cfg.stk DovetailStack.input =
    ((List.range round).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map (fun b => some (ULift.up b))
    )).reverse.flatten
  state : tm2cfg.stk DovetailStack.state =
    ((List.range round).map (fun i => (instanceConfig gen i round).state)).reverse
  output : tm2cfg.stk DovetailStack.output =
    ((List.range round).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten
  workR : tm2cfg.stk DovetailStack.workR =
    ((List.range round).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkR cfg (round - i)
    )).reverse.flatten
  workL : tm2cfg.stk DovetailStack.workL =
    ((List.range round).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkL cfg (round - i)
    )).reverse.flatten
  target_preserved : tm2cfg.stk DovetailStack.target = target
  save_empty :
    tm2cfg.stk DovetailStack.saveTarget = [] ∧
    tm2cfg.stk DovetailStack.saveCounter = [] ∧
    tm2cfg.stk DovetailStack.saveInput = [] ∧
    tm2cfg.stk DovetailStack.saveState = [] ∧
    tm2cfg.stk DovetailStack.saveWorkL = [] ∧
    tm2cfg.stk DovetailStack.saveWorkR = [] ∧
    tm2cfg.stk DovetailStack.saveOutput = []

set_option linter.unusedSectionVars true
end Dovetailing

end RandomisedGeneration
