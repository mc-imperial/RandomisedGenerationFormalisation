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
set_option linter.unusedSectionVars false

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw] [Inhabited Γw] [FinEnum Q]

/-- Popping the leading none from the quiescent stack format gives the
    check phase format with the topmost instance's data exposed. -/
lemma quiescent_format_tail {α : Type*} (f : ℕ → List (Option α)) (n : ℕ) (hn : 0 < n) :
    (((List.range n).map (fun i => [none] ++ f i)).reverse.flatten).tail =
    f (n - 1) ++
    ((List.range (n - 1)).map (fun i => [none] ++ f i)).reverse.flatten := by
  rw [show n = (n - 1) + 1 by omega]
  simp [List.range_succ, List.map_append, List.reverse_append,
        List.flatten_cons]

/-- The quiescent format for none-separated stacks starts with none when nonempty. -/
lemma quiescent_format_head {α : Type*} (f : ℕ → List (Option α)) (n : ℕ) (hn : 0 < n) :
    ((List.range n).map (fun i => [none] ++ f i)).reverse.flatten =
    none :: (f (n - 1) ++
    ((List.range (n - 1)).map (fun i => [none] ++ f i)).reverse.flatten) := by
  rw [show n = (n - 1) + 1 by omega]
  simp [List.range_succ, List.map_append, List.reverse_append,
        List.flatten_cons]

/-- Mid-check-phase invariant: j instances have been checked (newest j),
    with their segments moved to save stacks. The remaining (round - j)
    oldest instances remain on the main stacks.

    The check phase processes instances from newest to oldest (top of stack).
    Before the loop, check_stripSeparators stripped the newest instance's
    leading separator and pushed none to each save stack. Subsequent
    separators are consumed by the save routines and pushed to save.

    At check_iterateInstances, the main stacks have no leading separator:
    the data of the next instance to check is directly on top.

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
    if round - j = 0 then []
    else
      ((instanceConfig gen (round - j - 1) round).output.map some) ++
      ((List.range (round - j - 1)).map (fun i =>
        [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten
  input : tm2cfg.stk DovetailStack.input =
    if round - j = 0 then []
    else
      let cfg := instanceConfig gen (round - j - 1) round
      ((Nat.bits (round - j - 1)).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)) ++
      ((List.range (round - j - 1)).map (fun i =>
        let cfg := instanceConfig gen i round
        [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
          (fun b => some (ULift.up b)))).reverse.flatten
  workR : tm2cfg.stk DovetailStack.workR =
    if round - j = 0 then []
    else
      let cfg := instanceConfig gen (round - j - 1) round
      [some (cfg.work cfg.workIndex)] ++ segWorkR cfg (round - (round - j - 1)) ++
      ((List.range (round - j - 1)).map (fun i =>
        let cfg := instanceConfig gen i round
        [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkR cfg (round - i)
      )).reverse.flatten
  workL : tm2cfg.stk DovetailStack.workL =
    if round - j = 0 then []
    else
      let cfg := instanceConfig gen (round - j - 1) round
      [some (cfg.work cfg.workIndex)] ++ segWorkL cfg (round - (round - j - 1)) ++
      ((List.range (round - j - 1)).map (fun i =>
        let cfg := instanceConfig gen i round
        [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkL cfg (round - i)
      )).reverse.flatten
  -- ═══ Save stacks ═══
  saveState : tm2cfg.stk DovetailStack.saveState =
    ((List.range j).map
      (fun k => (instanceConfig gen (round - 1 - k) round).state)).reverse
  saveOutput : tm2cfg.stk DovetailStack.saveOutput =
    ((List.range j).map (fun k =>
      let i := round - 1 - k
      (instanceConfig gen i round).output.map some ++ [none])).flatten ++ [none]
  saveInput : tm2cfg.stk DovetailStack.saveInput =
    ((List.range j).map (fun k =>
      let i := round - 1 - k
      let cfg := instanceConfig gen i round
      ((Nat.bits i).drop cfg.inputIndex).map
        (fun b => some (ULift.up b)) ++ [none])).flatten ++ [none]
  saveWorkR : tm2cfg.stk DovetailStack.saveWorkR =
    ((List.range j).map (fun k =>
      let i := round - 1 - k
      let cfg := instanceConfig gen i round
      segWorkR cfg (round - i) ++ [some (cfg.work cfg.workIndex)] ++ [none]
    )).flatten ++ [none]
  saveWorkL : tm2cfg.stk DovetailStack.saveWorkL =
    ((List.range j).map (fun k =>
      let i := round - 1 - k
      let cfg := instanceConfig gen i round
      segWorkL cfg (round - i) ++ [some (cfg.work cfg.workIndex)] ++ [none]
    )).flatten ++ [none]
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
  sorry -- Check that this lemma statement is actually good.
  -- The proof below may be partially usable if so.

  -- -- Unfold IsHalting to get gen.δ = none
  -- unfold IsHalting step at hHalts
  -- -- Let inst = instanceConfig gen (round - j - 1) round for brevity
  -- set inst := instanceConfig gen (round - j - 1) round with hinst
  -- -- Get the top-of-stack facts from hInv
  -- have hNonempty : round - j ≠ 0 := by omega
  -- have hTop : tm2cfg.stk DovetailStack.state =
  --     inst.state :: ((List.range (round - j - 1)).map
  --       (fun i => (instanceConfig gen i round).state)).reverse := by
  --   rw [hInv.state]
  --   rw [show round - j = (round - j - 1) + 1 by omega]
  --   simp [List.range_succ, List.map_append, List.reverse_append]
  --   rfl
  -- have hOutputTop : tm2cfg.stk DovetailStack.output =
  --     [none] ++ inst.output.map some ++
  --     ((List.range (round - j - 1)).map (fun i =>
  --       [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten := by
  --   rw [hInv.output]
  --   rw [show round - j = (round - j - 1) + 1 by omega]
  --   simp [List.range_succ, List.map_append, List.reverse_append]
  --   rfl
  -- have hInputTop : (tm2cfg.stk DovetailStack.input).head? =
  --     some (some (ULift.up (inst.input inst.inputIndex))) := by
  --   rw [hInv.input]
  --   rw [show round - j = (round - j - 1) + 1 by omega]
  --   simp [List.range_succ, List.map_append, List.reverse_append,
  --         instanceConfig, Nat.bits]
  --   sorry -- needs careful unfolding of instanceConfig input encoding
  -- have hWorkRTop : (tm2cfg.stk DovetailStack.workR).head? =
  --     some (some (inst.work inst.workIndex)) := by
  --   sorry -- needs splitSegments lemma for workR
  -- -- Construct tm2cfg'
  -- refine ⟨{
  --   l   := some DovetailLabel.check_compareOutput
  --   var := { tm2cfg.var with
  --     peekQ     := some inst.state
  --     transQ    := some inst.state
  --     inputBit  := ULift.up (inst.input inst.inputIndex)
  --     peekInput := some (some (ULift.up (inst.input inst.inputIndex)))
  --     transW    := some (inst.work inst.workIndex)
  --     peekWorkR := some (some (inst.work inst.workIndex))
  --     transHalted := true
  --     transIDir := InputTapeDirection.N
  --     transWDir := WorkTapeDirection.N
  --     transOut  := none }
  --   stk := Function.update
  --             (Function.update
  --               (Function.update tm2cfg.stk
  --                 DovetailStack.state
  --                 (inst.state :: ((List.range (round - j - 1)).map
  --                   (fun i => (instanceConfig gen i round).state)).reverse))
  --               DovetailStack.output
  --               (inst.output.map some ++
  --               ((List.range (round - j - 1)).map (fun i =>
  --                 [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten))
  --             DovetailStack.saveOutput
  --             (none :: tm2cfg.stk DovetailStack.saveOutput)
  -- }, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- -- preserved stacks (refine_1 through refine_11)
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · simp only [Function.update, reduceCtorEq, ↓reduceDIte]
  -- · -- Define the intermediate cfg after check_iterateInstances → check_testHalting
  --   set tm2cfg_mid : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  --     { l   := some DovetailLabel.check_testHalting
  --       var := { tm2cfg.var with
  --         peekQ  := some inst.state
  --         transQ := some inst.state }
  --       stk := Function.update tm2cfg.stk DovetailStack.state
  --         ((List.range (round - j - 1)).map
  --           (fun i => (instanceConfig gen i round).state)).reverse }
  --   apply Relation.ReflTransGen.trans (b := tm2cfg_mid)
  --   · -- Step 1: check_iterateInstances → check_testHalting
  --     apply Relation.ReflTransGen.single
  --     rw [Turing.TM2.step.eq_def]
  --     simp only [dovetailMachine]
  --     obtain ⟨l, var, stk⟩ := tm2cfg
  --     cases hInv.label_eq
  --     simp only [Turing.TM2.stepAux, check_iterateInstances]
  --     have hTop' : stk DovetailStack.state =
  --         inst.state :: (List.map (fun i => (instanceConfig gen i round).state)
  --           (List.range (round - j - 1))).reverse := hTop
  --     simp only [hTop', List.head?_cons, Option.isNone_some, cond_false, List.tail_cons,
  --       Option.mem_def, tm2cfg_mid]
  --   · -- Step 2: check_testHalting → check_compareOutput
  --     apply Relation.ReflTransGen.single
  --     rw [Turing.TM2.step.eq_def]
  --     simp only [dovetailMachine, Turing.TM2.stepAux, check_testHalting, tm2cfg_mid]
  --     have hInputTop' : (Function.update tm2cfg.stk DovetailStack.state
  --         ((List.range (round - j - 1)).map
  --           (fun i => (instanceConfig gen i round).state)).reverse
  --         DovetailStack.input).head? =
  --         some (some { down := inst.input inst.inputIndex }) := by
  --       simp [Function.update, reduceCtorEq, hInputTop]
  --     have hWorkRTop' : (Function.update tm2cfg.stk DovetailStack.state
  --         ((List.range (round - j - 1)).map
  --           (fun i => (instanceConfig gen i round).state)).reverse
  --         DovetailStack.workR).head? =
  --         some (some (inst.work inst.workIndex)) := by
  --       simp [Function.update, reduceCtorEq, hWorkRTop]
  --     rw [hInputTop', hWorkRTop']
  --     simp only [applyDelta, Option.getD_some]
  --     have hDelta : gen.δ inst.state (inst.input inst.inputIndex)
  --         (inst.work inst.workIndex) = none := by
  --       revert hHalts
  --       intro h
  --       split at h <;> simp_all
  --     rw [hDelta]
  --     simp only [cond_true, Option.mem_def]
  --     have hOutputTop' : (Function.update tm2cfg.stk DovetailStack.state
  --         ((List.range (round - j - 1)).map
  --           (fun i => (instanceConfig gen i round).state)).reverse
  --         DovetailStack.output) =
  --         [none] ++ List.map some inst.output ++
  --         (List.map (fun i => [none] ++ List.map some (instanceConfig gen i round).output)
  --           (List.range (round - j - 1))).reverse.flatten := by
  --       simp [Function.update, reduceCtorEq, hOutputTop]
  --     simp only [Option.getD_some]
  --     simp only [Option.some.injEq, Turing.TM2.Cfg.mk.injEq]
  --     refine ⟨trivial, trivial, ?_⟩
  --     funext k
  --     cases k <;> simp [Function.update, reduceCtorEq, hOutputTop, List.tail_cons]

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
  sorry -- Unclear whether this lemma is good as stated.

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
    the TM2 halts. -/
lemma check_compareOutput_halts_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hLabel : tm2cfg.l = some DovetailLabel.check_compareOutput)
    (hTarget : tm2cfg.stk DovetailStack.target = target)
    (hOutput : ∃ rest : List (Option Γo),
      tm2cfg.stk DovetailStack.output = target.reverse.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none)) :
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
  have hHalt_j_rearranged : IsHalting gen (instanceConfig gen (round - j - 1) round) := by
    have : round - 1 - j = round - j - 1 := by omega
    rw [this] at hHalt_j
    exact hHalt_j
  let idx := round - 1 - j
  let cfg := instanceConfig gen idx round
  -- Step 1: check_iterateInstances → check_testHalting (one step)
  obtain ⟨tm2cfg₁, hLabel₁, hPeekQ₁, hState₁, hOutput₁, hInput₁, hWorkL₁, hWorkR₁,
    hCounter₁, hTarget₁, hSaveState₁, hSaveInput₁, hSaveWorkL₁, hSaveWorkR₁,
    hSaveOutput₁, hSaveTarget₁, hSaveCounter₁, hReach₁⟩ :=
    checkPhase_iterate_to_testHalting gen target round j tm2cfg hInv hj
  -- Step 2: check_testHalting detects halting, pushes state back,
  -- goes to check_compareOutput
  have h_inv_tm2cfg₁ : CheckPhaseInvariant gen target round j tm2cfg₁ := by
    sorry
  obtain ⟨tm2cfg₂, hLabel₂, hState₂, hOutput₂, hSaveOutput₂, hInput₂, hWorkL₂,
    hWorkR₂, hCounter₂, hTarget₂, hSaveState₂, hSaveInput₂, hSaveWorkL₂,
    hSaveWorkR₂, hSaveTarget₂, hSaveCounter₂, hReach₂⟩ :=
    checkPhase_testHalting_halts gen target round j tm2cfg₁
      h_inv_tm2cfg₁
      hj hHalt_j_rearranged
  -- Step 3: check_compareOutput matches and halts
  have hOutEq : cfg.output = target.reverse :=
    List.reverse_injective (by rw [List.reverse_reverse]; exact hOut_j)
  -- The output stack at tm2cfg₂ has cfg.output.map some on top
  -- which equals target.reverse.map some
  -- The rest starts with none (next instance's separator) or is empty
  have hOutputMatch : ∃ rest : List (Option Γo),
      tm2cfg₂.stk DovetailStack.output = target.reverse.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none) := by
    rw [hOutput₂]
    have h_idx : round - 1 - j = round - j - 1 := by omega
    refine ⟨((List.range (round - j - 1)).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten, ?_, ?_⟩
    · congr 1
      rw [← h_idx, hOutEq]
    · by_cases h : round - j - 1 = 0
      · left; simp [h]
      · right
        have h_eq := quiescent_format_head
          (fun i => (instanceConfig gen i round).output.map some) (round - j - 1) (by omega)
        have : (List.map (fun i => [none] ++ List.map some (instanceConfig gen i round).output)
            (List.range (round - j - 1))).reverse.flatten =
          (List.map (fun i => none :: List.map some (instanceConfig gen i round).output)
            (List.range (round - j - 1))).reverse.flatten := by
          congr 1
        rw [this]
        simp only [List.nil_append, List.cons_append] at h_eq
        rw [h_eq]
        rfl
  have hTarget₂' : tm2cfg₂.stk DovetailStack.target = target := by
    rw [hTarget₂, hTarget₁, hInv.target_preserved]
  obtain ⟨tm2cfg', hHalt', hReach'⟩ :=
    check_compareOutput_halts_on_match gen target tm2cfg₂ hLabel₂ hTarget₂' hOutputMatch
  exact ⟨tm2cfg', hHalt',
    Relation.ReflTransGen.trans hReach₁ (Relation.ReflTransGen.trans hReach₂ hReach')⟩

/-- When the quiescent invariant holds and there are instances (round > 0),
    check_stripSeparators takes one TM2 step to reach check_iterateInstances,
    popping the leading none from input/workL/workR/output and pushing none
    to each save stack. -/
lemma check_stripSeparators_step
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round tm2cfg)
    (hRound : 0 < round) :
    Turing.TM2.step (dovetailMachine gen) tm2cfg = some
      { l := some DovetailLabel.check_iterateInstances
        var := { tm2cfg.var with
          peekQ := (tm2cfg.stk DovetailStack.state).head? }
        stk := fun k => match k with
          | DovetailStack.input      => (tm2cfg.stk DovetailStack.input).tail
          | DovetailStack.workL      => (tm2cfg.stk DovetailStack.workL).tail
          | DovetailStack.workR      => (tm2cfg.stk DovetailStack.workR).tail
          | DovetailStack.output     => (tm2cfg.stk DovetailStack.output).tail
          | DovetailStack.saveInput  => [none]
          | DovetailStack.saveWorkL  => [none]
          | DovetailStack.saveWorkR  => [none]
          | DovetailStack.saveOutput => [none]
          | other                    => tm2cfg.stk other
      } := by
  cases tm2cfg with | mk l v S =>
  simp only at hInv ⊢
  rw [show l = some DovetailLabel.check_stripSeparators from hInv.label_eq]
  -- State stack is nonempty
  have hStateNe : S DovetailStack.state ≠ [] := by
    have := hInv.state
    simp only at this
    rw [this]
    simp [List.reverse_eq_nil_iff, List.map_eq_nil_iff]
    omega
  obtain ⟨q, qs, hState⟩ := List.exists_cons_of_ne_nil hStateNe
  obtain ⟨hST, hSC, hSI, hSS, hSWL, hSWR, hSO⟩ := hInv.save_empty
  have hInputHead : S DovetailStack.input =
      none :: (S DovetailStack.input).tail := by
    have hInputEq : S DovetailStack.input = none :: (S DovetailStack.input).tail := by
        have h := hInv.input
        simp only at h
        rw [h]
        rw [quiescent_format_head _ round hRound]
        simp [List.tail_cons]
    simp only at hInputEq
    rw [hInputEq]
    simp [List.tail_cons]
  have hOutputHead : S DovetailStack.output =
      none :: (S DovetailStack.output).tail := by
    have h := hInv.output
    simp only at h
    rw [h]
    rw [quiescent_format_head _ round hRound]
    simp [List.tail_cons]
  simp only [Turing.TM2.step, dovetailMachine, check_stripSeparators, Option.some.injEq]
  have hWorkRHead : S DovetailStack.workR = none :: (S DovetailStack.workR).tail := by
    have h := hInv.workR
    simp only at h
    rw [h]
    simp only [List.cons_append, List.nil_append]
    have h_eq := quiescent_format_head
      (fun i => [some ((instanceConfig gen i round).work (instanceConfig gen i round).workIndex)] ++
        segWorkR (instanceConfig gen i round) (round - i)) round hRound
    simp only [List.nil_append, List.cons_append] at h_eq
    rw [h_eq]
    simp [List.tail_cons]
  have hWorkLHead : S DovetailStack.workL = none :: (S DovetailStack.workL).tail := by
    have h := hInv.workL
    simp only at h
    rw [h]
    simp only [List.cons_append, List.nil_append]
    have h_eq := quiescent_format_head
        (fun i => [some ((instanceConfig gen i round).work
          (instanceConfig gen i round).workIndex)] ++
          segWorkL (instanceConfig gen i round) (round - i)) round hRound
    simp only [List.nil_append, List.cons_append] at h_eq
    rw [h_eq]
    simp [List.tail_cons]
  simp only [Turing.TM2.stepAux, hState, List.head?_cons, Option.isNone_some, cond_false]
  rw [hInputHead, hOutputHead, hWorkLHead, hWorkRHead]
  simp only [List.tail_cons]
  congr 1
  funext k
  cases k <;> simp only [Function.update, reduceCtorEq, ↓reduceDIte, List.cons.injEq, true_and]
  · simp only at hSI; exact hSI
  · simp only at hSWL; exact hSWL
  · simp only at hSWR; exact hSWR
  · simp only at hSO; exact hSO

/-- The quiescent format for none-separated stacks starts with none when nonempty. -/
lemma quiescent_to_checkPhase
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (round : ℕ)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hInv : QuiescentInvariant gen target round tm2cfg)
    (hRound : 0 < round) :
    ∃ tm2cfg',
      CheckPhaseInvariant gen target round 0 tm2cfg' ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  -- State stack is non-empty
  have hStateNe : tm2cfg.stk DovetailStack.state ≠ [] := by
    rw [hInv.state]
    simp [List.reverse_eq_nil_iff, List.map_eq_nil_iff]
    omega
  -- The quiescent stacks start with none
  have hOutputEq : tm2cfg.stk DovetailStack.output =
      none :: ((instanceConfig gen (round - 1) round).output.map some ++
      ((List.range (round - 1)).map (fun i =>
        [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten) := by
    rw [hInv.output]
    exact quiescent_format_head _ round hRound
  have hInputEq : tm2cfg.stk DovetailStack.input =
      none :: (let cfg := instanceConfig gen (round - 1) round
      ((Nat.bits (round - 1)).drop cfg.inputIndex).map (fun b => some (ULift.up b)) ++
      ((List.range (round - 1)).map (fun i =>
        let cfg := instanceConfig gen i round
        [none] ++ ((Nat.bits i).drop cfg.inputIndex).map
          (fun b => some (ULift.up b)))).reverse.flatten) := by
    rw [hInv.input]
    exact quiescent_format_head _ round hRound
  have hWorkREq : tm2cfg.stk DovetailStack.workR =
        none :: (let cfg := instanceConfig gen (round - 1) round
          [some (cfg.work cfg.workIndex)] ++ segWorkR cfg (round - (round - 1)) ++
          ((List.range (round - 1)).map (fun i =>
            let cfg := instanceConfig gen i round
            [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkR cfg (round - i)
          )).reverse.flatten) := by
    rw [hInv.workR]
    exact quiescent_format_head _ round hRound
  have hWorkLEq : tm2cfg.stk DovetailStack.workL =
      none :: (let cfg := instanceConfig gen (round - 1) round
      [some (cfg.work cfg.workIndex)] ++ segWorkL cfg (round - (round - 1)) ++
      ((List.range (round - 1)).map (fun i =>
        let cfg := instanceConfig gen i round
        [none] ++ [some (cfg.work cfg.workIndex)] ++ segWorkL cfg (round - i)
      )).reverse.flatten) := by
    rw [hInv.workL]
    exact quiescent_format_head _ round hRound
  -- Simulate the TM2 step and construct the CheckPhaseInvariant
  refine ⟨{
    l := some DovetailLabel.check_iterateInstances
    var := { tm2cfg.var with peekQ := (tm2cfg.stk DovetailStack.state).head? }
    stk := fun k => match k with
      | DovetailStack.input      => (tm2cfg.stk DovetailStack.input).tail
      | DovetailStack.workL      => (tm2cfg.stk DovetailStack.workL).tail
      | DovetailStack.workR      => (tm2cfg.stk DovetailStack.workR).tail
      | DovetailStack.output     => (tm2cfg.stk DovetailStack.output).tail
      | DovetailStack.saveInput  => [none]
      | DovetailStack.saveWorkL  => [none]
      | DovetailStack.saveWorkR  => [none]
      | DovetailStack.saveOutput => [none]
      | other                    => tm2cfg.stk other
  }, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  -- label_eq
  · rfl
  -- hj
  · exact Nat.zero_le _
  -- noMatch
  · intro i hi; omega
  -- state
  · simp only [Nat.sub_zero]; exact hInv.state
  -- output
  · simp only [Nat.sub_zero, show round ≠ 0 by omega, ↓reduceIte]
    rw [hOutputEq]; rfl
  -- input
  · simp only [Nat.sub_zero, show round ≠ 0 by omega, ↓reduceIte]
    rw [hInputEq]; rfl
  -- workR
  · simp only [Nat.sub_zero, show round ≠ 0 by omega, ↓reduceIte]
    rw [hWorkREq]; rfl
  -- workL
  · simp only [Nat.sub_zero, show round ≠ 0 by omega, ↓reduceIte]
    rw [hWorkLEq]; rfl
  -- saveState
  · simp only [List.range_zero, List.map_nil, List.reverse_nil]
    exact hInv.save_empty.2.2.2.1
  -- saveOutput
  · simp [List.range_zero]
  -- saveInput
  · simp [List.range_zero]
  -- saveWorkR
  · simp [List.range_zero]
  -- saveWorkL
  · simp [List.range_zero]
  -- counter
  · exact hInv.counter
  -- target_preserved
  · exact hInv.target_preserved
  -- saveTarget_empty
  · exact hInv.save_empty.1
  -- saveCounter_empty
  · exact hInv.save_empty.2.1
  -- Reaches: one TM2 step
  · have hStep := check_stripSeparators_step gen target round tm2cfg hInv hRound
    exact Relation.ReflTransGen.single hStep

set_option linter.unusedSectionVars true
end Dovetailing

end RandomisedGeneration
