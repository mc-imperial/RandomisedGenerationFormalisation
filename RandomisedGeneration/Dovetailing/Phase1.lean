import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language
import RandomisedGeneration.Dovetailing.AbstractMachine
import RandomisedGeneration.Dovetailing.DovetailingTM2
import RandomisedGeneration.Dovetailing.GlobalInvariants

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

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
  workR_head : ∀ i (hi : i < round - j),
    let cfg := instanceConfig gen i round
    let seg := (splitSegments (tm2cfg.stk DovetailStack.workR)).get ⟨i, by
      have := workR_len; omega⟩
    seg.headI = cfg.work cfg.workIndex
  workL_len : (splitSegments (tm2cfg.stk DovetailStack.workL)).length = round - j
  workL : ∀ i (hi : i < round - j),
    workLMatches gen (instanceConfig gen i round)
      ((splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by omega⟩)
      (round - i)
  workL_head : ∀ i (hi : i < round - j),
    let cfg := instanceConfig gen i round
    let seg := (splitSegments (tm2cfg.stk DovetailStack.workL)).get ⟨i, by
      have := workL_len; omega⟩
    seg.headI = cfg.work cfg.workIndex

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

/-- When `CheckPhaseInvariant` holds with `j < round`, the machine takes a single step
    from `check_iterateInstances` to `check_testHalting`.

    Since `j < round`, the state stack is nonempty — its top element is the state of
    instance `round - j - 1` (the next instance to be checked). The machine peeks it
    (storing it in `peekQ`), pops it, and transitions to `check_testHalting`.

    All stacks other than `DovetailStack.state` are unchanged. -/
lemma checkPhase_iterate_to_testHalting
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round) :
    ∃ tm2cfg',
      tm2cfg'.l = some DovetailLabel.check_testHalting ∧
      tm2cfg'.var.peekQ = some (instanceConfig gen (round - j - 1) round).state ∧
      tm2cfg'.stk DovetailStack.state =
        ((List.range (round - j - 1)).map
          (fun i => (instanceConfig gen i round).state)).reverse ∧
      -- all other stacks preserved
      tm2cfg'.stk DovetailStack.output    = tm2cfg.stk DovetailStack.output ∧
      tm2cfg'.stk DovetailStack.input     = tm2cfg.stk DovetailStack.input ∧
      tm2cfg'.stk DovetailStack.workL     = tm2cfg.stk DovetailStack.workL ∧
      tm2cfg'.stk DovetailStack.workR     = tm2cfg.stk DovetailStack.workR ∧
      tm2cfg'.stk DovetailStack.counter   = tm2cfg.stk DovetailStack.counter ∧
      tm2cfg'.stk DovetailStack.target    = tm2cfg.stk DovetailStack.target ∧
      tm2cfg'.stk DovetailStack.saveState  = tm2cfg.stk DovetailStack.saveState ∧
      tm2cfg'.stk DovetailStack.saveInput  = tm2cfg.stk DovetailStack.saveInput ∧
      tm2cfg'.stk DovetailStack.saveWorkL  = tm2cfg.stk DovetailStack.saveWorkL ∧
      tm2cfg'.stk DovetailStack.saveWorkR  = tm2cfg.stk DovetailStack.saveWorkR ∧
      tm2cfg'.stk DovetailStack.saveOutput = tm2cfg.stk DovetailStack.saveOutput ∧
      tm2cfg'.stk DovetailStack.saveTarget = tm2cfg.stk DovetailStack.saveTarget ∧
      tm2cfg'.stk DovetailStack.saveCounter = tm2cfg.stk DovetailStack.saveCounter ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  -- The state stack is nonempty by hj
  have hState := hInv.state
  have hNonempty : (round - j) ≠ 0 := by omega
  -- The top of the state stack is instance round-j-1's state
  have hTop : tm2cfg.stk DovetailStack.state =
      (instanceConfig gen (round - j - 1) round).state ::
      ((List.range (round - j - 1)).map
        (fun i => (instanceConfig gen i round).state)).reverse := by
    rw [hState]
    rw [show round - j = (round - j - 1) + 1 by omega]
    simp [List.range_succ, List.map_append, List.reverse_append]
  -- Construct tm2cfg'
  refine ⟨{
    l   := some DovetailLabel.check_testHalting
    var := { tm2cfg.var with
      peekQ  := some (instanceConfig gen (round - j - 1) round).state
      transQ := some (instanceConfig gen (round - j - 1) round).state }
    stk := Function.update tm2cfg.stk DovetailStack.state
      ((List.range (round - j - 1)).map
        (fun i => (instanceConfig gen i round).state)).reverse
  }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  all_goals simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · apply Relation.ReflTransGen.single
    rw [Turing.TM2.step.eq_def]
    simp only [dovetailMachine, check_iterateInstances]
    obtain ⟨l, var, stk⟩ := tm2cfg
    cases hInv.label_eq
    simp only [Turing.TM2.stepAux]
    rw [show stk DovetailStack.state = _ from hTop]
    simp only [List.head?_cons, Option.isNone_some, cond_false, List.tail_cons]
    simp only [Option.mem_def]

/-- When `check_testHalting` fires and the instance is halting, the machine reaches
    `check_compareOutput`. The state is pushed back, the output `none` separator is
    popped, and `none` is pushed to `saveOutput`. -/
lemma checkPhase_testHalting_halts
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hHalts : IsHalting gen (instanceConfig gen (round - j - 1) round)) :
    ∃ tm2cfg',
      tm2cfg'.l = some DovetailLabel.check_compareOutput ∧
      tm2cfg'.stk DovetailStack.state =
        (instanceConfig gen (round - j - 1) round).state ::
        ((List.range (round - j - 1)).map
          (fun i => (instanceConfig gen i round).state)).reverse ∧
      tm2cfg'.stk DovetailStack.output =
        (instanceConfig gen (round - j - 1) round).output.map some ++
        ((List.range (round - j - 1)).map (fun i =>
          [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten ∧
      tm2cfg'.stk DovetailStack.saveOutput =
        none :: tm2cfg.stk DovetailStack.saveOutput ∧
      tm2cfg'.stk DovetailStack.input      = tm2cfg.stk DovetailStack.input ∧
      tm2cfg'.stk DovetailStack.workL      = tm2cfg.stk DovetailStack.workL ∧
      tm2cfg'.stk DovetailStack.workR      = tm2cfg.stk DovetailStack.workR ∧
      tm2cfg'.stk DovetailStack.counter    = tm2cfg.stk DovetailStack.counter ∧
      tm2cfg'.stk DovetailStack.target     = tm2cfg.stk DovetailStack.target ∧
      tm2cfg'.stk DovetailStack.saveState  = tm2cfg.stk DovetailStack.saveState ∧
      tm2cfg'.stk DovetailStack.saveInput  = tm2cfg.stk DovetailStack.saveInput ∧
      tm2cfg'.stk DovetailStack.saveWorkL  = tm2cfg.stk DovetailStack.saveWorkL ∧
      tm2cfg'.stk DovetailStack.saveWorkR  = tm2cfg.stk DovetailStack.saveWorkR ∧
      tm2cfg'.stk DovetailStack.saveTarget = tm2cfg.stk DovetailStack.saveTarget ∧
      tm2cfg'.stk DovetailStack.saveCounter = tm2cfg.stk DovetailStack.saveCounter ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  -- Unfold IsHalting to get gen.δ = none
  unfold IsHalting step at hHalts
  -- Let inst = instanceConfig gen (round - j - 1) round for brevity
  set inst := instanceConfig gen (round - j - 1) round with hinst
  -- Get the top-of-stack facts from hInv
  have hNonempty : round - j ≠ 0 := by omega
  have hTop : tm2cfg.stk DovetailStack.state =
      inst.state :: ((List.range (round - j - 1)).map
        (fun i => (instanceConfig gen i round).state)).reverse := by
    rw [hInv.state]
    rw [show round - j = (round - j - 1) + 1 by omega]
    simp [List.range_succ, List.map_append, List.reverse_append]
    rfl
  have hOutputTop : tm2cfg.stk DovetailStack.output =
      [none] ++ inst.output.map some ++
      ((List.range (round - j - 1)).map (fun i =>
        [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten := by
    rw [hInv.output]
    rw [show round - j = (round - j - 1) + 1 by omega]
    simp [List.range_succ, List.map_append, List.reverse_append]
    rfl
  have hInputTop : (tm2cfg.stk DovetailStack.input).head? =
      some (some (ULift.up (inst.input inst.inputIndex))) := by
    rw [hInv.input]
    rw [show round - j = (round - j - 1) + 1 by omega]
    simp [List.range_succ, List.map_append, List.reverse_append,
          instanceConfig, Nat.bits]
    sorry -- needs careful unfolding of instanceConfig input encoding
  have hWorkRTop : (tm2cfg.stk DovetailStack.workR).head? =
      some (some (inst.work inst.workIndex)) := by
    sorry -- needs splitSegments lemma for workR
  -- Construct tm2cfg'
  refine ⟨{
    l   := some DovetailLabel.check_compareOutput
    var := { tm2cfg.var with
      peekQ     := some inst.state
      transQ    := some inst.state
      inputBit  := ULift.up (inst.input inst.inputIndex)
      peekInput := some (some (ULift.up (inst.input inst.inputIndex)))
      transW    := some (inst.work inst.workIndex)
      peekWorkR := some (some (inst.work inst.workIndex))
      transHalted := true
      transIDir := InputTapeDirection.N
      transWDir := WorkTapeDirection.N
      transOut  := none }
    stk := Function.update
              (Function.update
                (Function.update tm2cfg.stk
                  DovetailStack.state
                  (inst.state :: ((List.range (round - j - 1)).map
                    (fun i => (instanceConfig gen i round).state)).reverse))
                DovetailStack.output
                (inst.output.map some ++
                ((List.range (round - j - 1)).map (fun i =>
                  [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten))
              DovetailStack.saveOutput
              (none :: tm2cfg.stk DovetailStack.saveOutput)
  }, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- preserved stacks (refine_1 through refine_11)
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  · -- Define the intermediate cfg after check_iterateInstances → check_testHalting
    set tm2cfg_mid : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
      { l   := some DovetailLabel.check_testHalting
        var := { tm2cfg.var with
          peekQ  := some inst.state
          transQ := some inst.state }
        stk := Function.update tm2cfg.stk DovetailStack.state
          ((List.range (round - j - 1)).map
            (fun i => (instanceConfig gen i round).state)).reverse }
    apply Relation.ReflTransGen.trans (b := tm2cfg_mid)
    · -- Step 1: check_iterateInstances → check_testHalting
      apply Relation.ReflTransGen.single
      rw [Turing.TM2.step.eq_def]
      simp only [dovetailMachine]
      obtain ⟨l, var, stk⟩ := tm2cfg
      cases hInv.label_eq
      simp only [Turing.TM2.stepAux, check_iterateInstances]
      have hTop' : stk DovetailStack.state =
          inst.state :: (List.map (fun i => (instanceConfig gen i round).state)
            (List.range (round - j - 1))).reverse := hTop
      simp only [hTop', List.head?_cons, Option.isNone_some, cond_false, List.tail_cons,
        Option.mem_def, tm2cfg_mid]
    · -- Step 2: check_testHalting → check_compareOutput
      apply Relation.ReflTransGen.single
      rw [Turing.TM2.step.eq_def]
      simp only [dovetailMachine, Turing.TM2.stepAux, check_testHalting, tm2cfg_mid]
      have hInputTop' : (Function.update tm2cfg.stk DovetailStack.state
          ((List.range (round - j - 1)).map
            (fun i => (instanceConfig gen i round).state)).reverse
          DovetailStack.input).head? =
          some (some { down := inst.input inst.inputIndex }) := by
        simp [Function.update, reduceCtorEq, hInputTop]
      have hWorkRTop' : (Function.update tm2cfg.stk DovetailStack.state
          ((List.range (round - j - 1)).map
            (fun i => (instanceConfig gen i round).state)).reverse
          DovetailStack.workR).head? =
          some (some (inst.work inst.workIndex)) := by
        simp [Function.update, reduceCtorEq, hWorkRTop]
      rw [hInputTop', hWorkRTop']
      simp only [applyDelta, Option.getD_some]
      have hDelta : gen.δ inst.state (inst.input inst.inputIndex)
          (inst.work inst.workIndex) = none := by
        revert hHalts
        intro h
        split at h <;> simp_all
      rw [hDelta]
      simp only [cond_true, Option.mem_def]
      have hOutputTop' : (Function.update tm2cfg.stk DovetailStack.state
          ((List.range (round - j - 1)).map
            (fun i => (instanceConfig gen i round).state)).reverse
          DovetailStack.output) =
          [none] ++ List.map some inst.output ++
          (List.map (fun i => [none] ++ List.map some (instanceConfig gen i round).output)
            (List.range (round - j - 1))).reverse.flatten := by
        simp [Function.update, reduceCtorEq, hOutputTop]
      simp only [Option.getD_some]
      simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq]
      refine ⟨trivial, trivial, ?_⟩
      funext k
      cases k <;> simp [Function.update, reduceCtorEq, hOutputTop, List.tail_cons]

/-- When `check_testHalting` fires and the instance is not halting, the machine reaches
    `check_saveInstance_state`. The state is pushed back unchanged. -/
lemma checkPhase_testHalting_not_halts
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round j : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : CheckPhaseInvariant gen target round j tm2cfg)
    (hj : j < round)
    (hNotHalts : ¬IsHalting gen (instanceConfig gen (round - j - 1) round)) :
    ∃ tm2cfg',
      tm2cfg'.l = some DovetailLabel.check_saveInstance_state ∧
      tm2cfg'.stk DovetailStack.state =
        (instanceConfig gen (round - j - 1) round).state ::
        ((List.range (round - j - 1)).map
          (fun i => (instanceConfig gen i round).state)).reverse ∧
      -- all stacks preserved
      tm2cfg'.stk DovetailStack.output     = tm2cfg.stk DovetailStack.output ∧
      tm2cfg'.stk DovetailStack.input      = tm2cfg.stk DovetailStack.input ∧
      tm2cfg'.stk DovetailStack.workL      = tm2cfg.stk DovetailStack.workL ∧
      tm2cfg'.stk DovetailStack.workR      = tm2cfg.stk DovetailStack.workR ∧
      tm2cfg'.stk DovetailStack.counter    = tm2cfg.stk DovetailStack.counter ∧
      tm2cfg'.stk DovetailStack.target     = tm2cfg.stk DovetailStack.target ∧
      tm2cfg'.stk DovetailStack.saveState  = tm2cfg.stk DovetailStack.saveState ∧
      tm2cfg'.stk DovetailStack.saveOutput = tm2cfg.stk DovetailStack.saveOutput ∧
      tm2cfg'.stk DovetailStack.saveInput  = tm2cfg.stk DovetailStack.saveInput ∧
      tm2cfg'.stk DovetailStack.saveWorkL  = tm2cfg.stk DovetailStack.saveWorkL ∧
      tm2cfg'.stk DovetailStack.saveWorkR  = tm2cfg.stk DovetailStack.saveWorkR ∧
      tm2cfg'.stk DovetailStack.saveTarget = tm2cfg.stk DovetailStack.saveTarget ∧
      tm2cfg'.stk DovetailStack.saveCounter = tm2cfg.stk DovetailStack.saveCounter ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  sorry






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
  workR_head := by
    intro i hi
    simp only [Nat.sub_zero] at hi
    exact hInv.workR_head i hi
  workL_len := by simp [hInv.workL_len]
  workL := hInv.workL
  workL_head := by
    intro i hi
    simp only [Nat.sub_zero] at hi
    exact hInv.workL_head i hi
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

end Dovetailing

end RandomisedGeneration
