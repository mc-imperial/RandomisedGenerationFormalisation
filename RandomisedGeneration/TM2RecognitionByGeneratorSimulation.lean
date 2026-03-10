import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
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
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round
  workL : ∀ i (hi : i < round),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  target_preserved : tm2cfg.stk DovetailStack.target = target
  save_empty :
    tm2cfg.stk DovetailStack.saveTarget = [] ∧
    tm2cfg.stk DovetailStack.saveCounter = [] ∧
    tm2cfg.stk DovetailStack.saveInput = [] ∧
    tm2cfg.stk DovetailStack.saveState = [] ∧
    tm2cfg.stk DovetailStack.saveWorkL = [] ∧
    tm2cfg.stk DovetailStack.saveWorkR = [] ∧
    tm2cfg.stk DovetailStack.saveOutput = []

/-- Mid-check-phase invariant: j instances have been checked (newest j),
    with their segments moved to save stacks. The remaining (round - j)
    oldest instances remain on the main stacks.

    The check phase processes instances from newest to oldest (top of stack).
    After checking j instances, the main stacks hold instances 0..round-j-1
    and the save stacks hold instances round-j..round-1.

    None of the checked instances had matching output. -/
structure CheckPhaseInvariant
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop where
  label_eq : tm2cfg.l = some DovetailLabel.check_iterateInstances
  hj : j ≤ round
  noMatch : ∀ i, round - j ≤ i → i < round →
    ¬(IsHalting gen (instanceConfig gen i round) ∧
      (instanceConfig gen i round).output.reverse = target)
  -- ═══ Main stacks: oldest round-j instances (indices 0..round-j-1) ═══
  state : tm2cfg.stk DovetailStack.state =
    ((List.range (round - j)).map
      (fun i => (instanceConfig gen i round).state)).reverse
  output : tm2cfg.stk DovetailStack.output =
    ((List.range (round - j)).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten
  input : tm2cfg.stk DovetailStack.input =
    ((List.range (round - j)).map (fun i =>
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)))).reverse.flatten
  workR_len : (splitSegments (tm2cfg.stk DovetailStack.workR)).length = round - j
  workR : ∀ i (hi : i < round - j),
    workRMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by omega⟩)
      (round - i)
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round - j
  workL : ∀ i (hi : i < round - j),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  -- ═══ Save stacks: newest j instances (indices round-j..round-1) ═══
  -- saveState: j entries. First processed = index round-1 (was on top of main).
  -- It gets pushed to saveState first, so it's at the bottom.
  -- Last processed = index round-j, on top of saveState.
  saveState : tm2cfg.stk DovetailStack.saveState =
    (List.range j).map
      (fun k => (instanceConfig gen (round - j + k) round).state)
  -- saveOutput: j segments, same indexing as saveState
  saveOutput : tm2cfg.stk DovetailStack.saveOutput =
    ((List.range j).map (fun k =>
      let i := round - j + k
      [none] ++ (instanceConfig gen i round).output.map some)).flatten
  -- saveInput: j segments
  saveInput : tm2cfg.stk DovetailStack.saveInput =
    ((List.range j).map (fun k =>
      let i := round - j + k
      let cfg := instanceConfig gen i round
      [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)))).flatten
  -- saveWorkR/saveWorkL: j segments
  saveWorkR_len : (splitSegments (tm2cfg.stk DovetailStack.saveWorkR)).length = j
  saveWorkR : ∀ k (hk : k < j),
    workRMatches gen (instanceConfig gen (round - j + k) round)
      ((splitSegments (tm2cfg.stk DovetailStack.saveWorkR)).get ⟨k, by omega⟩)
      (round - (round - j + k))
  saveWorkL_len : (splitSegments (tm2cfg.stk DovetailStack.saveWorkL)).length = j
  saveWorkL : ∀ k (hk : k < j),
    workLMatches gen (instanceConfig gen (round - j + k) round)
      ((splitSegments (tm2cfg.stk DovetailStack.saveWorkL)).get ⟨k, by omega⟩)
      (round - (round - j + k))
  -- ═══ Preserved ═══
  counter : tm2cfg.stk DovetailStack.counter = (Nat.bits round).map ULift.up
  target_preserved : tm2cfg.stk DovetailStack.target = target
  saveTarget_empty : tm2cfg.stk DovetailStack.saveTarget = []
  saveCounter_empty : tm2cfg.stk DovetailStack.saveCounter = []

set_option linter.unusedSectionVars false
lemma quiescentInvariant_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    QuiescentInvariant gen target 0 DovetailLabel.check_iterateInstances (dovetailInit target) where
  label_eq := by
    rfl
  counter := by
    simp [dovetailInit, Turing.TM2.init, Function.update]
  input := by
    rfl
  state := by
    simp [dovetailInit, Turing.TM2.init, Function.update]
  output := by
    rfl
  workR_len := by
    simp [splitSegments, dovetailInit, Turing.TM2.init]
  workR := by
    intro i hi
    omega
  workL_len := by simp [splitSegments, dovetailInit, Turing.TM2.init]
  workL := by
    intro i hi
    omega
  target_preserved := by
    rfl
  save_empty := by
    simp [dovetailInit, Turing.TM2.init]

/-- The abstract DovetailState is "in correspondence" with a TM2 config
    when the QuiescentInvariant holds at check_iterateInstances.
    This is the bisimulation relation between the abstract dovetail machine
    and the concrete TM2 implementation. -/
def InCorrespondence
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    : Prop :=
  QuiescentInvariant gen target ds.instances.length DovetailLabel.check_iterateInstances tm2cfg

/-- The initial configs are in correspondence. -/
lemma inCorrespondence_init
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    InCorrespondence gen target initDovetailState (dovetailInit target) := by
  exact quiescentInvariant_init gen target

/-- From check_iterateInstances with j instances already processed and no match among them,
    processing one more non-matching instance advances to j+1. -/
lemma checkPhase_advance_no_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hNoMatch_j : ¬(IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
      (instanceConfig gen (round - 1 - j) round).output.reverse = target)) :
    ∃ tm2cfg',
      CheckPhaseInvariant gen target round (j + 1) tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- If check_compareOutput is entered with matching output on top of the stacks,
    the TM2 halts. The output stack has the output symbols reversed
    (last symbol on top) followed by a separator or end. -/
lemma check_compareOutput_halts_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hLabel : tm2cfg.l = some DovetailLabel.check_compareOutput)
    (hTarget : tm2cfg.stk DovetailStack.target = target)
    -- Output stack: reversed output on top, then none or empty
    (hOutput : ∃ rest : List (Option Γo),
      tm2cfg.stk DovetailStack.output = target.reverse.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none))
    (hSaveTarget : tm2cfg.stk DovetailStack.saveTarget = [])
    (hSaveOutput : tm2cfg.stk DovetailStack.saveOutput = []) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- From check_iterateInstances with j instances already processed, if instance j matches,
    the TM2 reaches a halted config. -/
lemma checkPhase_halt_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hMatch_j : IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
      (instanceConfig gen (round - 1 - j) round).output.reverse = target) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨hHalt_j, hOut_j⟩ := hMatch_j
  let idx := round - 1 - j
  let cfg := instanceConfig gen idx round
  -- Step 1: check_iterateInstances pops state, goes to check_testHalting
  -- The top of state stack is (instanceConfig gen idx round).state
  -- Step 2: check_testHalting peeks input, peeks workR, applies delta, finds halting
  -- Step 3: pushes state back, goes to check_compareOutput
  -- These are a bounded number of TM2 steps from tm2cfg to some tm2cfg_co
  -- at label check_compareOutput
  have hSteps : ∃ tm2cfg_co : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q),
      tm2cfg_co.l = some DovetailLabel.check_compareOutput ∧
      tm2cfg_co.stk DovetailStack.target = target ∧
      (∃ rest : List (Option Γo), tm2cfg_co.stk DovetailStack.output =
        cfg.output.map some ++ rest) ∧
      tm2cfg_co.stk DovetailStack.saveTarget = [] ∧
      tm2cfg_co.stk DovetailStack.saveOutput = [] ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_co := by
    sorry
  obtain ⟨tm2cfg_co, hLabel_co, hTarget_co, ⟨rest, hOutput_co⟩,
    hSaveTarget_co, hSaveOutput_co, hReach_co⟩ := hSteps
  -- Step 4: check_compareOutput compares and halts
  -- output on stack is cfg.output.map some ++ rest (newest output symbol on top)
  -- target on stack is target
  -- cfg.output.reverse = target (from hOut_j)
  -- So the comparison succeeds
  have hOutEq : cfg.output = target.reverse :=
    List.reverse_injective (by rw [List.reverse_reverse]; exact hOut_j)
  obtain ⟨tm2cfg', hHalt', hReach'⟩ := check_compareOutput_halts_on_match gen
    target tm2cfg_co
    hLabel_co hTarget_co
    ⟨rest, by rw [hOutput_co, hOutEq], sorry⟩
    hSaveTarget_co hSaveOutput_co
  exact ⟨tm2cfg', hHalt', Relation.ReflTransGen.trans hReach_co hReach'⟩

/-- A QuiescentInvariant at check_iterateInstances gives a CheckPhaseInvariant at j=0. -/
lemma quiescent_to_checkPhase
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round DovetailLabel.check_iterateInstances tm2cfg) :
    CheckPhaseInvariant gen target round 0 tm2cfg where
  label_eq := hInv.label_eq
  hj := Nat.zero_le _
  noMatch := by intro i hi; omega
  state := by simp [hInv.state]
  output := by simp [hInv.output]
  input := by simp [hInv.input]
  workR_len := by simp [hInv.workR_len]
  workR := hInv.workR
  workL_len := by simp [hInv.workL_len]
  workL := hInv.workL
  saveState := by
    simp only [tsub_zero, List.range_zero, List.map_nil]
    exact hInv.save_empty.2.2.2.1
  saveOutput := by
    simp only [tsub_zero, List.cons_append, List.nil_append, List.range_zero,
      List.map_nil, List.flatten_nil]
    exact hInv.save_empty.2.2.2.2.2.2
  saveInput := by
    simp only [tsub_zero, List.map_drop, List.cons_append, List.nil_append,
      List.range_zero, List.map_nil, List.flatten_nil]
    exact hInv.save_empty.2.2.1
  saveWorkR_len := by
    simp only [splitSegments, List.length_eq_zero_iff]
    have h := hInv.save_empty.2.2.2.2.2.1
    rw [h]
  saveWorkR := by intro k hk; omega
  saveWorkL_len := by
    simp only [splitSegments, List.length_eq_zero_iff]
    have h := hInv.save_empty.2.2.2.2.1
    rw [h]
  saveWorkL := by intro k hk; omega
  counter := hInv.counter
  target_preserved := hInv.target_preserved
  saveTarget_empty := hInv.save_empty.1
  saveCounter_empty := hInv.save_empty.2.1

/-- If in correspondence and some instance has halting output matching
    the target (reversed, due to stack ordering), the TM2 reaches a
    halted configuration. This is the key lemma for the backward direction:
    DovetailRecognises → TM2 halts. -/
lemma inCorrespondence_halt
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hCorr : InCorrespondence gen target ds tm2cfg)
    (hMatch : ∃ i, i < ds.instances.length ∧
      IsHalting gen (instanceConfig gen i ds.instances.length) ∧
      (instanceConfig gen i ds.instances.length).output.reverse = target) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨k, hk_lt, hk_halt, hk_out⟩ := hMatch
  let round := ds.instances.length
  have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
  suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q)),
      round - j = d →
      j ≤ round →
      CheckPhaseInvariant gen target round j tm2cfg_j →
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
      (∃ i, i < round - j ∧
        IsHalting gen (instanceConfig gen i round) ∧
        (instanceConfig gen i round).output.reverse = target) →
      ∃ tm2cfg',
        tm2cfg'.l = none ∧
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' by
    exact this round 0 tm2cfg (by omega) (Nat.zero_le _) hCheck₀
      Relation.ReflTransGen.refl ⟨k, by omega, hk_halt, hk_out⟩
  intro d
  induction d with
  | zero =>
    intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, _, _⟩
    omega
  | succ d ih =>
    intro j tm2cfg_j hd hj hInv_j hReach_j ⟨i, hi_lt, hi_halt, hi_out⟩
    -- The next instance to check is round - 1 - j
    by_cases hMatch_j : IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
        (instanceConfig gen (round - 1 - j) round).output.reverse = target
    · have hj_lt : j < round := by omega
      obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
        checkPhase_halt_on_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
      exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_j h_reaches'⟩
    · have hj_lt : j < round := by omega
      obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
        checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hMatch_j
      have hi_ne : i ≠ round - 1 - j := by
        intro heq; rw [heq] at hi_halt hi_out; exact hMatch_j ⟨hi_halt, hi_out⟩
      exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
        (Relation.ReflTransGen.trans hReach_j hReach_next)
        ⟨i, by omega, hi_halt, hi_out⟩

/-- From CheckPhaseInvariant with all instances checked (j = round) and no match,
    restoring save stacks reaches spawn_copyCounter with QuiescentInvariant. -/
lemma checkPhase_complete_to_pushNewConfig
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round round tm2cfg) :
    ∃ tm2cfg',
      QuiescentInvariant gen target round DovetailLabel.spawn_copyCounter tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- From spawn_copyCounter, spawn a new instance and step all,
    reaching check_iterateInstances at round+1. -/
lemma pushNewConfig_step_to_next_check_iterateInstances
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round DovetailLabel.spawn_copyCounter tm2cfg) :
    ∃ tm2cfg',
      QuiescentInvariant gen target (round + 1) DovetailLabel.check_iterateInstances tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry

/-- If in correspondence and no instance matches, one abstract dovetailStep
    corresponds to finitely many TM2 steps, reaching a new correspondence.
    This is the simulation lemma: one abstract round = one concrete round. -/
lemma inCorrespondence_step
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hCorr : InCorrespondence gen target ds tm2cfg)
    (hNoMatch : ∀ i, i < ds.instances.length →
      ¬(IsHalting gen (instanceConfig gen i ds.instances.length) ∧
        (instanceConfig gen i ds.instances.length).output.reverse = target)) :
    ∃ tm2cfg',
      InCorrespondence gen target (dovetailStep gen ds) tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  let round := ds.instances.length
  -- Phase 1: Check all instances, find no match, advance to j = round
  have hCheck₀ := quiescent_to_checkPhase gen target round tm2cfg hCorr
  have hCheckAll : ∃ tm2cfg_check,
      CheckPhaseInvariant gen target round round tm2cfg_check ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check := by
    suffices ∀ d j (tm2cfg_j : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
          DovetailLabel (DovetailSigma Γw Γo Q)),
        round - j = d →
        j ≤ round →
        CheckPhaseInvariant gen target round j tm2cfg_j →
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_j →
        ∃ tm2cfg_check,
          CheckPhaseInvariant gen target round round tm2cfg_check ∧
          Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg_check by
      exact this round 0 tm2cfg rfl (Nat.zero_le _) hCheck₀ Relation.ReflTransGen.refl
    intro d
    induction d with
    | zero =>
      intro j tm2cfg_j hd hj hInv_j hReach_j
      have : j = round := by omega
      subst this
      exact ⟨tm2cfg_j, hInv_j, hReach_j⟩
    | succ d ih =>
      intro j tm2cfg_j hd hj hInv_j hReach_j
      have hj_lt : j < round := by omega
      -- Instance round-1-j doesn't match (from hNoMatch)
      have hNoMatch_j : ¬(IsHalting gen (instanceConfig gen (round - 1 - j) round) ∧
          (instanceConfig gen (round - 1 - j) round).output.reverse = target) :=
        hNoMatch (round - 1 - j) (by omega)
      obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
        checkPhase_advance_no_match gen target round j tm2cfg_j hInv_j hj_lt hNoMatch_j
      exact ih (j + 1) tm2cfg_next (by omega) (by omega) hInv_next
        (Relation.ReflTransGen.trans hReach_j hReach_next)
  -- Phase 2: From CheckPhaseInvariant at j=round, restore to pushNewConfig
  obtain ⟨tm2cfg_check, hInv_check, hReach_check⟩ := hCheckAll
  obtain ⟨tm2cfg_push, hInv_push, hReach_push⟩ :=
    checkPhase_complete_to_pushNewConfig gen target round tm2cfg_check hInv_check
  -- Phase 3: From pushNewConfig, spawn + step + restore + increment to next check_iterateInstances
  obtain ⟨tm2cfg_next, hInv_next, hReach_next⟩ :=
    pushNewConfig_step_to_next_check_iterateInstances gen target round tm2cfg_push hInv_push
  -- Connect everything
  refine ⟨tm2cfg_next, ?_, ?_⟩
  · -- InCorrespondence gen target (dovetailStep gen ds) tm2cfg_next
    -- This is QuiescentInvariant gen target (round+1) check_iterateInstances tm2cfg_next
    -- which is hInv_next, but we need to show round+1 = (dovetailStep gen ds).instances.length
    change QuiescentInvariant gen target (dovetailStep gen ds).instances.length
      DovetailLabel.check_iterateInstances tm2cfg_next
    rw [show (dovetailStep gen ds).instances.length = round + 1 from by
      simp [dovetailStep, round]]
    exact hInv_next
  · exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans hReach_check hReach_push) hReach_next

lemma dovetailTM2_halts_implies_DovetailRecognises
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom →
    DovetailRecognises gen w.reverse := by
  -- One idea is to prove this by contrapositive.
  sorry

/-- Backward: if DovetailRecognises, then the TM2 halts. -/
lemma DovetailRecognises_implies_dovetailTM2_halts
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    DovetailRecognises gen w.reverse →
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom := by
  intro ⟨n, i, cfg, h_inst, h_halt, h_out⟩
  suffices ∃ tm2cfg' : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
        DovetailLabel (DovetailSigma Γw Γo Q),
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
        (dovetailInit w) tm2cfg' by
    obtain ⟨tm2cfg', h_halt', h_reaches⟩ := this
    rw [Turing.TM2.eval, Part.dom_iff_mem]
    have h_halt_step : Turing.TM2.step (dovetailMachine gen) tm2cfg' = none := by
      cases tm2cfg'; simp_all [Turing.TM2.step]
    exact ⟨tm2cfg'.stk DovetailStack.target,
      Part.mem_map _ (Turing.mem_eval.mpr ⟨h_reaches, h_halt_step⟩)⟩
  suffices ∀ r,
      ∃ (tm2cfg_r : Turing.TM2.Cfg (stackAlphabet Γw Γo Q)
            DovetailLabel (DovetailSigma Γw Γo Q)),
        (tm2cfg_r.l = none ∨
         InCorrespondence gen w
           ((dovetailStep gen)^[r] initDovetailState) tm2cfg_r) ∧
        Turing.Reaches (Turing.TM2.step (dovetailMachine gen))
          (dovetailInit w) tm2cfg_r by
    obtain ⟨tm2cfg_n, hAlt, hReach_n⟩ := this n
    rcases hAlt with h_halt' | hCorr_n
    · exact ⟨tm2cfg_n, h_halt', hReach_n⟩
    · have hi : i < n := by
        by_contra h; push_neg at h
        exact absurd h_inst (by
          rw [List.getElem?_eq_none (by rw [instances_length_after_steps]; omega)]
          exact Option.some_ne_none _ ∘ Eq.symm)
      have hMatch : ∃ j,
          j < ((dovetailStep gen)^[n] initDovetailState).instances.length ∧
          IsHalting gen (instanceConfig gen j
            ((dovetailStep gen)^[n] initDovetailState).instances.length) ∧
          (instanceConfig gen j
            ((dovetailStep gen)^[n] initDovetailState).instances.length).output.reverse = w := by
        rw [instances_length_after_steps]
        refine ⟨i, hi, ?_⟩
        rw [instance_config_after_steps gen n i hi] at h_inst
        have h_eq := Option.some.inj h_inst
        rw [← h_eq] at h_halt h_out
        exact ⟨h_halt, by simp only [instanceConfig]; rw [h_out, List.reverse_reverse]⟩
      obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
        inCorrespondence_halt gen w _ tm2cfg_n hCorr_n hMatch
      exact ⟨tm2cfg', h_halt', Relation.ReflTransGen.trans hReach_n h_reaches'⟩
  intro r
  induction r with
  | zero =>
    exact ⟨dovetailInit w, Or.inr (inCorrespondence_init gen w),
      Relation.ReflTransGen.refl⟩
  | succ r ih =>
    obtain ⟨tm2cfg_r, hAlt_r, hReach_r⟩ := ih
    rcases hAlt_r with h_halt_r | hCorr_r
    · exact ⟨tm2cfg_r, Or.inl h_halt_r, hReach_r⟩
    · by_cases hMatch_r : ∃ j,
          j < ((dovetailStep gen)^[r] initDovetailState).instances.length ∧
          IsHalting gen (instanceConfig gen j
            ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
          (instanceConfig gen j
            ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse = w
      · obtain ⟨tm2cfg', h_halt', h_reaches'⟩ :=
          inCorrespondence_halt gen w _ tm2cfg_r hCorr_r hMatch_r
        exact ⟨tm2cfg', Or.inl h_halt', Relation.ReflTransGen.trans hReach_r h_reaches'⟩
      · push_neg at hMatch_r
        have hNoMatch : ∀ j,
            j < ((dovetailStep gen)^[r] initDovetailState).instances.length →
            ¬(IsHalting gen (instanceConfig gen j
                ((dovetailStep gen)^[r] initDovetailState).instances.length) ∧
              (instanceConfig gen j
                ((dovetailStep gen)^[r] initDovetailState).instances.length).output.reverse
                = w) := by
          intro j hj ⟨hHalt, hOut⟩
          exact hMatch_r j hj hHalt hOut
        obtain ⟨tm2cfg_next, hCorr_next, hReach_next⟩ :=
          inCorrespondence_step gen w _ tm2cfg_r hCorr_r hNoMatch
        rw [show (dovetailStep gen)^[r + 1] initDovetailState =
            dovetailStep gen ((dovetailStep gen)^[r] initDovetailState) from
          by rw [Function.iterate_succ', Function.comp_apply]]
        exact ⟨tm2cfg_next, Or.inr hCorr_next,
          Relation.ReflTransGen.trans hReach_r hReach_next⟩

/-- The dovetail TM2 halts on input w iff DovetailRecognises gen w.reverse. -/
theorem dovetailTM2_halts_iff_DovetailRecognises
    (gen : Generator Γw Γo Q)
    (w : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target w).Dom ↔
    DovetailRecognises gen w.reverse :=
  ⟨dovetailTM2_halts_implies_DovetailRecognises gen w,
   DovetailRecognises_implies_dovetailTM2_halts gen w⟩

set_option linter.unusedSectionVars true
end Dovetailing

-- The dovetail   TM2 halts on input `target` iff `target` is in the generated language.
theorem dovetailMachine_recognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target target.reverse).Dom ↔
    target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
  rw [dovetailTM2_halts_iff_DovetailRecognises]
  simp only [List.reverse_reverse]
  rw [DovetailRecognises_iff_Computes]
  simp only [generatedLanguage, Set.mem_setOf_eq]

lemma every_generable_language_is_tm2_recognisable
    {Γ : Type u}
    [Inhabited Γ] [FinEnum Γ]
    (L : Language Γ)
    (hL : L ∈ generableLanguages) :
    L ∈ languagesRecognisedByTM2s := by
  obtain ⟨Γw, Q, hΓwfinenum, hQdec, gen, S_gen, hS_gen, hgen⟩ := hL
  haveI : DecidableEq Q := hQdec
  let gen' := @Generator.restrictToSupport Γw Γ Q hΓwfinenum _ _ gen S_gen hS_gen
  haveI : Fintype ↥S_gen := inferInstance
  haveI : DecidableEq ↥S_gen := inferInstance
  haveI : FinEnum ↥S_gen := FinEnum.ofList (Finset.univ.val.toList) (by simp)
  haveI : Inhabited ↥S_gen := ⟨gen'.init⟩
  haveI : ∀ k, Inhabited (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : ∀ k, Fintype (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : ∀ k, DecidableEq (stackAlphabet Γw Γ ↥S_gen k) :=
    fun k => by cases k <;> simp only [stackAlphabet] <;> infer_instance
  haveI : Inhabited Γw := ⟨gen.blank⟩
  refine ⟨
    DovetailStack,
    inferInstance,
    inferInstance,
    inferInstance,
    stackAlphabet Γw Γ ↥S_gen,
    inferInstance,
    inferInstance,
    inferInstance,
    rfl,
    DovetailLabel,
    inferInstance,
    inferInstance,
    DovetailSigma Γw Γ ↥S_gen,
    inferInstance,
    inferInstance,
    dovetailMachine gen',
    Finset.univ,
    ⟨Finset.mem_univ _, fun q _ => by
      cases q <;> simp only [dovetailMachine,
        check_iterateInstances, check_testHalting, check_compareOutput, check_compareOutput_restoreTarget, check_compareOutput_restoreOutput,
        check_saveInstance_state, check_saveInstance_input,
        check_saveInstance_workL, check_saveInstance_workR,
        check_saveInstance_output,
        check_restoreAll_state, check_restoreAll_input,
        check_restoreAll_workL, check_restoreAll_workR,
        check_restoreAll_output,
        spawn_copyCounter, spawn_restoreAndPush,
        step_iterateInstances, step_peekInput, step_peekWorkR, step_applyTransition, step_consumeInput,
        step_moveWorkHead,
        step_saveInstance_state, step_saveInstance_input, step_saveInstance_workL, step_saveInstance_workR,
        step_saveInstance_output, step_restoreAll_state, step_restoreAll_input,
        step_restoreAll_workL, step_restoreAll_workR, step_restoreAll_output,
        counter_increment, counter_increment_loop, counter_increment_restore,
        Turing.TM2.SupportsStmt] <;>
      simp (config := { decide := true })⟩,
    ?_⟩
  subst hgen
  ext input
  simp only [Set.mem_setOf_eq]
  have lang_eq : generatedLanguage gen S_gen hS_gen =
      generatedLanguage gen' Finset.univ (generator_supports_univ gen') := by
    ext w
    simp only [generatedLanguage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes gen S_gen hS_gen h⟩
    · rintro ⟨input, h⟩
      exact ⟨input, restrictToSupport_Computes_lift gen S_gen hS_gen h⟩
  rw [lang_eq]
  exact (dovetailMachine_recognises gen' input).symm

end RandomisedGeneration
