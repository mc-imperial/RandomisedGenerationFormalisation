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

lemma Nat.testBit_eq_bits_getD (n i : ℕ) :
    n.testBit i = (n.bits[i]?).getD false := by
  induction n using Nat.binaryRec generalizing i with
  | zero => simp [Nat.zero_bits]
  | bit b n h =>
    by_cases hn : n = 0 ∧ b = false
    · obtain ⟨rfl, rfl⟩ := hn
      simp [Nat.zero_bits]
    · push_neg at hn
      have hbn : n = 0 → b = true := by
        intro h0; cases b <;> simp_all
      rw [Nat.bits_append_bit _ _ hbn]
      cases i with
      | zero =>
        simp
      | succ i =>
        simp [Nat.testBit_bit_succ, h]

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
      (instanceConfig gen i round).output = target)
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
      tm2cfg'.var.transQ = some (instanceConfig gen (round - j - 1) round).state ∧
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
  }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
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

lemma instanceConfig_input (gen : Generator Γw Γo Q) (i round : ℕ) :
    (instanceConfig gen i round).input = Nat.testBit i := by
  unfold instanceConfig
  induction (round - i) with
  | zero => simp [stepNHalt, initConfig]
  | succ n ih =>
    simp only [stepNHalt]
    cases h : step gen (stepNHalt gen (initConfig gen (Nat.testBit i)) n) with
    | none => simp only; exact ih
    | some c => simp only; exact step_preserves_input h ▸ ih

/-- When `CheckPhaseInvariant` holds with `j < round` and the next instance is NOT halting,
    the machine reaches `check_saveInstance_state` from `check_iterateInstances`.

    This combines the step from check_iterateInstances to check_testHalting
    (popping state) with the step from check_testHalting to check_saveInstance_state
    (peeking input/workR, applying delta, detecting non-halt, pushing original state back).

    All stacks are preserved: check_testHalting peeks input and workR non-destructively,
    and pushes back the original state (from peekQ). -/
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
  -- Step 1: check_iterateInstances → check_testHalting
  obtain ⟨tm2cfg₁, hLabel₁, hPeekQ₁, hTransQ₁, hState₁, hOutput₁, hInput₁, hWorkL₁, hWorkR₁,
    hCounter₁, hTarget₁, hSaveState₁, hSaveInput₁, hSaveWorkL₁, hSaveWorkR₁,
    hSaveOutput₁, hSaveTarget₁, hSaveCounter₁, hReach₁⟩ :=
    checkPhase_iterate_to_testHalting gen target round j tm2cfg hInv hj
  set inst := instanceConfig gen (round - j - 1) round with hinst
  have hNotHalt : ∃ q' w' o id wd,
      gen.δ inst.state (inst.input inst.inputIndex) (inst.work inst.workIndex) =
        some (q', w', o, id, wd) := by
    unfold IsHalting step at hNotHalts
    by_contra h
    push_neg at h
    apply hNotHalts
    cases hδ : gen.δ inst.state (inst.input inst.inputIndex) (inst.work inst.workIndex) with
    | none =>
      rfl
    | some val =>
      exact absurd hδ (h val.1 val.2.1 val.2.2.1 val.2.2.2.1 val.2.2.2.2)
  obtain ⟨q', w', o, id, wd, hDelta⟩ := hNotHalt
  have hInputBit : (match (tm2cfg₁.stk DovetailStack.input).head? with
      | some (some b) => b.down
      | _ => false) = inst.input inst.inputIndex := by
    rw [hInput₁]
    have hInput := hInv.input
    have hne : round - j ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hInput
    rw [hInput]
    have hInstInput : inst.input = Nat.testBit (round - j - 1) :=
      instanceConfig_input gen (round - j - 1) round
    rw [hInstInput]
    -- Case split on whether there are remaining bits
    cases hBits : ((Nat.bits (round - j - 1)).drop inst.inputIndex) with
    | nil =>
      simp only [List.map_nil, List.nil_append]
      -- inputIndex ≥ length of bits, so testBit = false
      have hIdx : inst.inputIndex ≥ (Nat.bits (round - j - 1)).length := by
        by_contra h
        push_neg at h
        exact absurd (List.drop_eq_nil_iff.mp hBits) (by omega)
      symm
      rw [Nat.testBit_eq_bits_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]
      -- Now goal: (match head? of rest with ...) = false
      -- rest is either [] or starts with none
      by_cases h : round - j - 1 = 0
      · simp [h, List.range_zero]
      · have hRest := quiescent_format_head
          (fun i => let cfg := instanceConfig gen i round
            ((Nat.bits i).drop cfg.inputIndex).map (fun b => some (ULift.up.{u} b)))
          (round - j - 1) (by omega)
        simp only [List.nil_append, List.cons_append] at hRest
        have hHead := congr_arg List.head? hRest
        simp only [List.head?_cons] at hHead
        simp
        simp only [List.map_drop] at hHead ⊢
        simp [hHead]
    | cons b bs =>
      simp only [List.map_cons, List.cons_append, List.head?_cons]
      -- b is the inputIndex-th bit
      have hGet : (Nat.bits (round - j - 1))[inst.inputIndex]? = some b := by
        rw [← List.head?_drop, hBits]
        simp
      symm
      rw [Nat.testBit_eq_bits_getD, hGet]
      simp
  have hWorkHead : (match (tm2cfg₁.stk DovetailStack.workR).head? with
      | some (some x) => some x
      | _ => some gen.blank) = some (inst.work inst.workIndex) := by
    rw [hWorkR₁]
    have hWorkR := hInv.workR
    have hne : round - j ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hWorkR
    rw [hWorkR]
    simp
    rfl
  -- Step 2: check_testHalting → check_saveInstance_state (not halting branch)
  have hStep2 : ∃ tm2cfg₂,
      Turing.TM2.step (dovetailMachine gen) tm2cfg₁ = some tm2cfg₂ ∧
      tm2cfg₂.l = some DovetailLabel.check_saveInstance_state ∧
      tm2cfg₂.stk DovetailStack.state =
        inst.state :: ((List.range (round - j - 1)).map
          (fun i => (instanceConfig gen i round).state)).reverse ∧
      (∀ k, k ≠ DovetailStack.state →
        tm2cfg₂.stk k = tm2cfg₁.stk k) := by
    obtain ⟨l₁, v₁, stk₁⟩ := tm2cfg₁
    simp only at hLabel₁ hPeekQ₁ hTransQ₁ hState₁ hWorkHead hInputBit ⊢
    subst hLabel₁
    rw [Turing.TM2.step, dovetailMachine, check_testHalting]
    simp only [Turing.TM2.stepAux]
    unfold applyDelta
    cases hW : (stk₁ DovetailStack.workR).head? with
    | none =>
      cases hI : (stk₁ DovetailStack.input).head? with
      | none =>
        simp only [hW, hI] at hWorkHead hInputBit ⊢
        have hWorkHead' : gen.blank = inst.work inst.workIndex :=
          Option.some.inj hWorkHead
        have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank =
            some (q', w', o, id, wd) := by
          rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
        rw [hDelta', cond_false]
        refine ⟨_, rfl, rfl, ?_, ?_⟩
        · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
        · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
      | some ob => cases ob with
        | none =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hWorkHead' : gen.blank = inst.work inst.workIndex :=
            Option.some.inj hWorkHead
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank =
              some (q', w', o, id, wd) := by
            rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
          rw [hDelta', cond_false]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some b =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hWorkHead' : gen.blank = inst.work inst.workIndex :=
            Option.some.inj hWorkHead
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down gen.blank =
              some (q', w', o, id, wd) := by
            rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
          rw [hDelta', cond_false]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
    | some ow => cases ow with
      | none =>
        cases hI : (stk₁ DovetailStack.input).head? with
        | none =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hWorkHead' : gen.blank = inst.work inst.workIndex :=
            Option.some.inj hWorkHead
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank =
              some (q', w', o, id, wd) := by
            rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
          rw [hDelta', cond_false]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some ob => cases ob with
          | none =>
            simp only [hW, hI] at hWorkHead hInputBit ⊢
            have hWorkHead' : gen.blank = inst.work inst.workIndex :=
              Option.some.inj hWorkHead
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank =
                some (q', w', o, id, wd) := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
            rw [hDelta', cond_false]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
          | some b =>
            simp only [hW, hI] at hWorkHead hInputBit ⊢
            have hWorkHead' : gen.blank = inst.work inst.workIndex :=
              Option.some.inj hWorkHead
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down gen.blank =
                some (q', w', o, id, wd) := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead']; exact hDelta
            rw [hDelta', cond_false]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
      | some w =>
        cases hI : (stk₁ DovetailStack.input).head? with
        | none =>
          simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false w =
              some (q', w', o, id, wd) := by
            rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
          rw [hDelta', cond_false]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some ob => cases ob with
          | none =>
            simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) false w =
                some (q', w', o, id, wd) := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
            rw [hDelta', cond_false]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
          | some b =>
            simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down w =
                some (q', w', o, id, wd) := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
            rw [hDelta', cond_false]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
  -- Assemble the final result
  obtain ⟨tm2cfg₂, hStep₂, hLabel₂, hState₂, hOther₂⟩ := hStep2
  refine ⟨tm2cfg₂, hLabel₂, hState₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hOther₂ _ (by decide)]; exact hOutput₁
  · rw [hOther₂ _ (by decide)]; exact hInput₁
  · rw [hOther₂ _ (by decide)]; exact hWorkL₁
  · rw [hOther₂ _ (by decide)]; exact hWorkR₁
  · rw [hOther₂ _ (by decide)]; exact hCounter₁
  · rw [hOther₂ _ (by decide)]; exact hTarget₁
  · rw [hOther₂ _ (by decide)]; exact hSaveState₁
  · rw [hOther₂ _ (by decide)]; exact hSaveOutput₁
  · rw [hOther₂ _ (by decide)]; exact hSaveInput₁
  · rw [hOther₂ _ (by decide)]; exact hSaveWorkL₁
  · rw [hOther₂ _ (by decide)]; exact hSaveWorkR₁
  · rw [hOther₂ _ (by decide)]; exact hSaveTarget₁
  · rw [hOther₂ _ (by decide)]; exact hSaveCounter₁
  · exact Relation.ReflTransGen.trans hReach₁
      (Relation.ReflTransGen.single (by rw [Option.mem_def]; exact hStep₂))

/-- Helper: the check_compareOutput loop terminates with a halt when
    the remaining target and output match element by element. -/
private lemma check_compareOutput_loop
    (gen : Generator Γw Γo Q)
    (ts : List Γo)
    (rest : List (Option Γo))
    (hRest : rest = [] ∨ rest.head? = some none)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hLabel : tm2cfg.l = some DovetailLabel.check_compareOutput)
    (hTarget : tm2cfg.stk DovetailStack.target = ts)
    (hOutput : tm2cfg.stk DovetailStack.output = ts.map some ++ rest) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  induction ts generalizing tm2cfg with
  | nil =>
    simp only [List.map_nil, List.nil_append] at hOutput
    obtain ⟨l, v, stk⟩ := tm2cfg
    simp only at hTarget hOutput hLabel
    subst hLabel
    rcases hRest with rfl | hRest
    · -- rest = [], output stack is empty
      refine ⟨{
        l := none,
        var := { v with peekTarget := none, peekOut := none },
        stk := stk }, rfl, Relation.ReflTransGen.single ?_⟩
      rw [Option.mem_def, Turing.TM2.step]
      simp only [dovetailMachine, check_compareOutput, Turing.TM2.stepAux,
        hTarget, hOutput, List.head?_nil, Option.isNone_none, cond_true]
    · -- rest starts with none
      refine ⟨{ l := none, var := { v with peekTarget := none, peekOut := some none }, stk := stk },
        rfl, Relation.ReflTransGen.single ?_⟩
      rw [Option.mem_def, Turing.TM2.step]
      simp only [dovetailMachine, check_compareOutput, Turing.TM2.stepAux,
        hTarget, List.head?_nil, Option.isNone_none, cond_true, hOutput, hRest]
  | cons t ts ih =>
    obtain ⟨l, v, stk⟩ := tm2cfg
    simp only at hLabel hTarget hOutput
    subst hLabel
    simp only [List.map_cons, List.cons_append] at hOutput
    -- Construct the intermediate config after one TM2 step
    let stk' := Function.update
      (Function.update
        (Function.update
          (Function.update stk
            DovetailStack.target ts)
          DovetailStack.output (ts.map some ++ rest))
        DovetailStack.saveTarget (t :: stk DovetailStack.saveTarget))
      DovetailStack.saveOutput (some t :: stk DovetailStack.saveOutput)
    have hStep : Turing.TM2.step (dovetailMachine gen)
        { l := some DovetailLabel.check_compareOutput, var := v, stk := stk } =
      some {
        l := some DovetailLabel.check_compareOutput,
        var := { v with peekTarget := some t, peekOut := some (some t) },
        stk := stk' } := by
      rw [Turing.TM2.step]
      simp only [dovetailMachine, check_compareOutput, Turing.TM2.stepAux,
        hTarget, hOutput, List.head?_cons, Option.isNone_some, cond_false,
        decide_true, stk']
      simp only [cond_true, Option.getD_some, List.tail_cons]
      congr 1
      congr 1
      ext k
      cases k <;> simp [Function.update, reduceCtorEq, hOutput, List.tail_cons]
    -- Apply ih to the resulting config
    have hTarget' : stk' DovetailStack.target = ts := by
      simp [stk', Function.update, reduceCtorEq]
    have hOutput' : stk' DovetailStack.output = ts.map some ++ rest := by
      simp [stk', Function.update, reduceCtorEq]
    obtain ⟨tm2cfg', hHalt', hReach'⟩ := ih
      { l := some DovetailLabel.check_compareOutput,
        var := { v with peekTarget := some t, peekOut := some (some t) },
        stk := stk' }
      rfl hTarget' hOutput'
    exact ⟨tm2cfg', hHalt', Relation.ReflTransGen.head
      (by rw [Option.mem_def]; exact hStep) hReach'⟩

/-- If check_compareOutput is entered with matching output on top of the stacks,
    the TM2 halts. -/
lemma check_compareOutput_halts_on_match
    (gen : Generator Γw Γo Q)
    (target : List Γo)
    (tm2cfg : Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q))
    (hLabel : tm2cfg.l = some DovetailLabel.check_compareOutput)
    (hTarget : tm2cfg.stk DovetailStack.target = target)
    (hOutput : ∃ rest : List (Option Γo),
      tm2cfg.stk DovetailStack.output = target.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none)) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨rest, hOut, hRest⟩ := hOutput
  exact check_compareOutput_loop gen target rest hRest tm2cfg hLabel hTarget hOut

/-- When `CheckPhaseInvariant` holds with `j < round` and the next instance is halting,
    the machine reaches `check_compareOutput` from `check_iterateInstances`.

    This combines the step from check_iterateInstances to check_testHalting
    (popping state) with the step from check_testHalting to check_compareOutput
    (peeking input/workR, applying delta, detecting halt, pushing state back). -/
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
      tm2cfg'.stk DovetailStack.input      = tm2cfg.stk DovetailStack.input ∧
      tm2cfg'.stk DovetailStack.workL      = tm2cfg.stk DovetailStack.workL ∧
      tm2cfg'.stk DovetailStack.workR      = tm2cfg.stk DovetailStack.workR ∧
      tm2cfg'.stk DovetailStack.counter    = tm2cfg.stk DovetailStack.counter ∧
      tm2cfg'.stk DovetailStack.target     = tm2cfg.stk DovetailStack.target ∧
      tm2cfg'.stk DovetailStack.saveState  = tm2cfg.stk DovetailStack.saveState ∧
      tm2cfg'.stk DovetailStack.saveInput  = tm2cfg.stk DovetailStack.saveInput ∧
      tm2cfg'.stk DovetailStack.saveWorkL  = tm2cfg.stk DovetailStack.saveWorkL ∧
      tm2cfg'.stk DovetailStack.saveWorkR  = tm2cfg.stk DovetailStack.saveWorkR ∧
      tm2cfg'.stk DovetailStack.saveOutput = tm2cfg.stk DovetailStack.saveOutput ∧
      tm2cfg'.stk DovetailStack.saveTarget = tm2cfg.stk DovetailStack.saveTarget ∧
      tm2cfg'.stk DovetailStack.saveCounter = tm2cfg.stk DovetailStack.saveCounter ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  -- Step 1: check_iterateInstances → check_testHalting
  obtain ⟨tm2cfg₁, hLabel₁, hPeekQ₁, hTransQ₁, hState₁, hOutput₁, hInput₁, hWorkL₁, hWorkR₁,
    hCounter₁, hTarget₁, hSaveState₁, hSaveInput₁, hSaveWorkL₁, hSaveWorkR₁,
    hSaveOutput₁, hSaveTarget₁, hSaveCounter₁, hReach₁⟩ :=
    checkPhase_iterate_to_testHalting gen target round j tm2cfg hInv hj
  set inst := instanceConfig gen (round - j - 1) round with hinst
  have hDelta : gen.δ inst.state (inst.input inst.inputIndex)
      (inst.work inst.workIndex) = none := by
    unfold IsHalting step at hHalts; revert hHalts; intro h; split at h <;> simp_all
  have hInputBit : (match (tm2cfg₁.stk DovetailStack.input).head? with
      | some (some b) => b.down
      | _ => false) = inst.input inst.inputIndex := by
    rw [hInput₁]
    have hInput := hInv.input
    have hne : round - j ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hInput
    rw [hInput]
    -- Establish that inst.input = Nat.testBit (round - j - 1)
    have hInstInput : inst.input = Nat.testBit (round - j - 1) :=
      instanceConfig_input gen (round - j - 1) round
    rw [hInstInput]
    -- Case split on whether there are remaining bits
    cases hBits : ((Nat.bits (round - j - 1)).drop inst.inputIndex) with
    | nil =>
      simp only [List.map_nil, List.nil_append]
      -- inputIndex ≥ length of bits, so testBit = false
      have hIdx : inst.inputIndex ≥ (Nat.bits (round - j - 1)).length := by
        by_contra h
        push_neg at h
        exact absurd (List.drop_eq_nil_iff.mp hBits) (by omega)
      symm
      rw [Nat.testBit_eq_bits_getD, List.getElem?_eq_none (by omega)]
      simp only [Option.getD_none]
      -- Now goal: (match head? of rest with ...) = false
      -- rest is either [] or starts with none
      by_cases h : round - j - 1 = 0
      · simp [h, List.range_zero]
      · have hRest := quiescent_format_head
          (fun i => let cfg := instanceConfig gen i round
            ((Nat.bits i).drop cfg.inputIndex).map (fun b => some (ULift.up.{u} b)))
          (round - j - 1) (by omega)
        simp only [List.nil_append, List.cons_append] at hRest
        have hHead := congr_arg List.head? hRest
        simp only [List.head?_cons] at hHead
        simp
        simp only [List.map_drop] at hHead ⊢
        simp [hHead]
    | cons b bs =>
      simp only [List.map_cons, List.cons_append, List.head?_cons]
      -- b is the inputIndex-th bit
      have hGet : (Nat.bits (round - j - 1))[inst.inputIndex]? = some b := by
        rw [← List.head?_drop, hBits]
        simp
      symm
      rw [Nat.testBit_eq_bits_getD, hGet]
      simp
  have hWorkHead : (match (tm2cfg₁.stk DovetailStack.workR).head? with
      | some (some x) => some x
      | _ => some gen.blank) = some (inst.work inst.workIndex) := by
    rw [hWorkR₁]
    have hWorkR := hInv.workR
    have hne : round - j ≠ 0 := by omega
    simp only [hne, ↓reduceIte] at hWorkR
    rw [hWorkR]
    simp only [List.cons_append, List.head?_cons]
    rfl
  -- Step 2: compute what check_testHalting produces
  have hStep2 : ∃ tm2cfg₂,
      Turing.TM2.step (dovetailMachine gen) tm2cfg₁ = some tm2cfg₂ ∧
      tm2cfg₂.l = some DovetailLabel.check_compareOutput ∧
      tm2cfg₂.stk DovetailStack.state =
        inst.state :: ((List.range (round - j - 1)).map
          (fun i => (instanceConfig gen i round).state)).reverse ∧
      (∀ k, k ≠ DovetailStack.state →
        tm2cfg₂.stk k = tm2cfg₁.stk k) := by
    obtain ⟨l₁, v₁, stk₁⟩ := tm2cfg₁
    simp only at hLabel₁ hPeekQ₁ hTransQ₁ hState₁ hWorkHead hInputBit ⊢
    subst hLabel₁
    rw [Turing.TM2.step, dovetailMachine, check_testHalting]
    simp only [Turing.TM2.stepAux]
    unfold applyDelta
    cases hW : (stk₁ DovetailStack.workR).head? with
    | none =>
      cases hI : (stk₁ DovetailStack.input).head? with
      | none =>
        simp only [hW, hI] at hWorkHead hInputBit ⊢
        have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank = none := by
          rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
        rw [hDelta', cond_true]
        refine ⟨_, rfl, rfl, ?_, ?_⟩
        · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
        · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
      | some ob => cases ob with
        | none =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank = none := by
            rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
          rw [hDelta', cond_true]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some b =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down gen.blank = none := by
            rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
          rw [hDelta', cond_true]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
    | some ow => cases ow with
      | none =>
        cases hI : (stk₁ DovetailStack.input).head? with
        | none =>
          simp only [hW, hI] at hWorkHead hInputBit ⊢
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank = none := by
            rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
          rw [hDelta', cond_true]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some ob => cases ob with
          | none =>
            simp only [hW, hI] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) false gen.blank = none := by
              rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
            rw [hDelta', cond_true]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
          | some b =>
            simp only [hW, hI] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down gen.blank = none := by
              rw [hTransQ₁, Option.getD_some, hInputBit, Option.some.inj hWorkHead]; exact hDelta
            rw [hDelta', cond_true]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
      | some w =>
        cases hI : (stk₁ DovetailStack.input).head? with
        | none =>
          simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
          have hDelta' : gen.δ (v₁.transQ.getD gen.init) false w = none := by
            rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
          rw [hDelta', cond_true]
          refine ⟨_, rfl, rfl, ?_, ?_⟩
          · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
          · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
        | some ob => cases ob with
          | none =>
            simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) false w = none := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
            rw [hDelta', cond_true]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
          | some b =>
            simp only [hW, hI, Option.some.injEq] at hWorkHead hInputBit ⊢
            have hDelta' : gen.δ (v₁.transQ.getD gen.init) b.down w = none := by
              rw [hTransQ₁, Option.getD_some, hInputBit, hWorkHead]; exact hDelta
            rw [hDelta', cond_true]
            refine ⟨_, rfl, rfl, ?_, ?_⟩
            · simp only [Function.update, ↓reduceDIte, hPeekQ₁, Option.getD_some, hState₁]
            · intro k hk; simp only [Function.update]; split <;> [exact absurd ‹_› hk; rfl]
  obtain ⟨tm2cfg₂, hStep₂, hLabel₂, hState₂, hOther₂⟩ := hStep2
  refine ⟨tm2cfg₂, hLabel₂, hState₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- output
  · rw [hOther₂ _ (by decide), hOutput₁, hInv.output]
    simp only [show round - j ≠ 0 from by omega, ↓reduceIte]
    rfl
  -- preserved stacks (all go through hOther₂ then the chain back to tm2cfg)
  · rw [hOther₂ _ (by decide)]; exact hInput₁
  · rw [hOther₂ _ (by decide)]; exact hWorkL₁
  · rw [hOther₂ _ (by decide)]; exact hWorkR₁
  · rw [hOther₂ _ (by decide)]; exact hCounter₁
  · rw [hOther₂ _ (by decide)]; exact hTarget₁
  · rw [hOther₂ _ (by decide)]; exact hSaveState₁
  · rw [hOther₂ _ (by decide)]; exact hSaveInput₁
  · rw [hOther₂ _ (by decide)]; exact hSaveWorkL₁
  · rw [hOther₂ _ (by decide)]; exact hSaveWorkR₁
  · rw [hOther₂ _ (by decide)]; exact hSaveOutput₁
  · rw [hOther₂ _ (by decide)]; exact hSaveTarget₁
  · rw [hOther₂ _ (by decide)]; exact hSaveCounter₁
  -- Reaches
  · exact Relation.ReflTransGen.trans hReach₁
      (Relation.ReflTransGen.single (by rw [Option.mem_def]; exact hStep₂))

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
      (instanceConfig gen (round - 1 - j) round).output = target) :
    ∃ tm2cfg',
      tm2cfg'.l = none ∧
      Turing.Reaches (Turing.TM2.step (dovetailMachine gen)) tm2cfg tm2cfg' := by
  obtain ⟨hHalt_j, hOut_j⟩ := hMatch_j
  let idx := round - 1 - j
  let cfg := instanceConfig gen idx round
  -- Steps 1-2: check_iterateInstances → check_testHalting → check_compareOutput
  -- checkPhase_testHalting_halts takes the CheckPhaseInvariant directly
  have h_halting : IsHalting gen (instanceConfig gen (round - j - 1) round) := by
    have : round - 1 - j = round - j - 1 := by omega
    rw [this] at hHalt_j
    exact hHalt_j
  obtain ⟨tm2cfg₂, hLabel₂, hState₂, hOutput₂, hInput₂, hWorkL₂,
    hWorkR₂, hCounter₂, hTarget₂, hSaveState₂, hSaveInput₂, hSaveWorkL₂,
    hSaveWorkR₂, hSaveOutput₂, hSaveTarget₂, hSaveCounter₂, hReach₂⟩ :=
    checkPhase_testHalting_halts gen target round j tm2cfg hInv hj  h_halting
  -- Step 3: check_compareOutput matches and halts
  have h_idx : round - 1 - j = round - j - 1 := by omega
  have hOutputMatch : ∃ rest : List (Option Γo),
      tm2cfg₂.stk DovetailStack.output = target.map some ++ rest ∧
      (rest = [] ∨ rest.head? = some none) := by
    refine ⟨((List.range (round - j - 1)).map (fun i =>
      [none] ++ (instanceConfig gen i round).output.map some)).reverse.flatten, ?_, ?_⟩
    · rw [hOutput₂]
      congr 1
      rw [← h_idx]
      exact congr_arg (List.map some) hOut_j
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
    rw [hTarget₂, hInv.target_preserved]
  obtain ⟨tm2cfg', hHalt', hReach'⟩ :=
    check_compareOutput_halts_on_match gen target tm2cfg₂ hLabel₂ hTarget₂' hOutputMatch
  exact ⟨tm2cfg', hHalt', Relation.ReflTransGen.trans hReach₂ hReach'⟩

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
