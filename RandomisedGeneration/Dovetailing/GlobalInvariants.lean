import Mathlib
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Dovetailing.AbstractMachine
import RandomisedGeneration.Dovetailing.DovetailingTM2

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-- Split a none-separated stack into segments.
    The stack has newest data on top (head of list).
    Returns segments oldest-first (index 0 = oldest instance). -/
def splitSegments {α : Type u} : List (Option α) → List (List α)
  | [] => []
  | l =>
    let rec go (acc : List α) (rest : List (Option α)) : List (List α) :=
      match rest with
      | [] => [acc.reverse]
      | none :: tl => acc.reverse :: go [] tl
      | some x :: tl => go (x :: acc) tl
    let segs := match l with
      | none :: tl => go [] tl
      | _ => go [] l
    segs.reverse

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

/-- Quiescent invariant: the TM2 stacks correctly represent the state of
    the abstract dovetail machine at the start of a phase.

    Parameterised by:
    • gen: the generator being dovetailed
    • target: the word on the target stack (set at initialisation, never modified)
    • round: the number of completed rounds (= number of spawned instances)
    • label: the current TM2 label (check_iterateInstances or spawn_copyCounter)
    • tm2cfg: the TM2 configuration

    At round r, there are r instances. Instance i (0-indexed, 0 = oldest)
    has been stepped (r - i) times. Its abstract state is given by
    instanceConfig gen i r = stepNHalt gen (initConfig gen i.testBit) (r - i).

    The stacks encode all r instances' data with none separators between
    segments. Newest instance data is on top of each stack. -/
structure QuiescentInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (label : RandomisedGeneration.DovetailLabel)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop where
  label_eq : tm2cfg.l = some label
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
  workR_len : (splitSegments (tm2cfg.stk DovetailStack.workR)).length = round
  workR : ∀ i (hi : i < round),
    workRMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by omega⟩)
      (round - i)
  workR_head : ∀ i (hi : i < round),
    let cfg := instanceConfig gen i round
    let seg := (splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by
      have := workR_len; omega⟩
    seg.headI = cfg.work cfg.workIndex
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round
  workL : ∀ i (hi : i < round),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  workL_head : ∀ i (hi : i < round),
    let cfg := instanceConfig gen i round
    let seg := (splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by
      have := workL_len; omega⟩
    seg.headI = cfg.work cfg.workIndex
  target_preserved : tm2cfg.stk DovetailStack.target = target
  save_empty :
    tm2cfg.stk DovetailStack.saveTarget = [] ∧
    tm2cfg.stk DovetailStack.saveCounter = [] ∧
    tm2cfg.stk DovetailStack.saveInput = [] ∧
    tm2cfg.stk DovetailStack.saveState = [] ∧
    tm2cfg.stk DovetailStack.saveWorkL = [] ∧
    tm2cfg.stk DovetailStack.saveWorkR = [] ∧
    tm2cfg.stk DovetailStack.saveOutput = []

end Dovetailing

end RandomisedGeneration
