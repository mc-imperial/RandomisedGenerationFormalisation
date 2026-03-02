import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import Mathlib.Computability.TuringMachine
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

universe u

section Dovetailing

variable {Γw Γo Q : Type u}
variable [Inhabited Γo] [FinEnum Γo] [FinEnum Γw]

structure DovetailState where
  instances : List (Option (GenConfig Γw Γo Q))
  nextInput : ℕ

def dovetailStep
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { instances := ds.instances.map (fun cfg => cfg.bind (step gen))
                 ++ [some (initConfig gen (Nat.testBit ds.nextInput))]
    nextInput := ds.nextInput + 1 }

def initDovetailState : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { instances := []
    nextInput := 0 }

def DovetailRecognises
  (gen : Generator Γw Γo Q)
  (w : List Γo) : Prop :=
  ∃ (n i : Nat) (cfg : GenConfig Γw Γo Q),
    let state :=
      (dovetailStep gen)^[n]
        (initDovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
    let insts := state.instances
    insts[i]? = some (some cfg) ∧
    IsHalting gen cfg ∧
    cfg.output = w

-- The "already stepped" prefix
def steppedPrefix
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (Option (GenConfig Γw Γo Q)) :=
  (ds.instances.take k).map (·.bind (step gen))

-- The "not yet stepped" suffix
def pendingSuffix
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : List (Option (GenConfig Γw Γo Q)) :=
  ds.instances.drop k

-- The mid-round state at frontier k
def midRoundState
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q) :=
  { ds with instances := steppedPrefix gen ds k ++ pendingSuffix ds k }

-- At k=0, nothing has been stepped yet
lemma midRoundState_zero
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  midRoundState gen ds 0 = ds := by
  simp [midRoundState, steppedPrefix, pendingSuffix]

-- At k=length, everything has been stepped
lemma midRoundState_length
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  midRoundState gen ds ds.instances.length =
    { ds with instances := ds.instances.map (·.bind (step gen)) } := by
  simp [midRoundState, steppedPrefix, pendingSuffix, List.take_length, List.drop_length]

-- Advancing the frontier by one
lemma midRoundState_succ
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ)
  (hk : k < ds.instances.length) :
  midRoundState gen ds (k + 1) =
  { ds with instances :=
      (ds.instances.take k).map (·.bind (step gen))
      ++
      [ (ds.instances.get ⟨k, hk⟩).bind (step gen) ]
      ++
      ds.instances.drop (k + 1) } := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  congr 1
  rw [List.take_add_one, List.map_append]
  simp [List.getElem?_eq_getElem hk]

-- The full dovetailStep decomposes into midRoundState at length, then spawn
lemma dovetailStep_eq_spawn_of_midRound
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q)) :
  dovetailStep gen ds =
    { instances :=
        (midRoundState gen ds ds.instances.length).instances ++
          [some (initConfig gen (Nat.testBit ds.nextInput))]
      nextInput := ds.nextInput + 1 } := by
  simp [dovetailStep, midRoundState_length]

-- The length of instances is preserved by midRoundState
lemma midRoundState_length_eq
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k : ℕ) :
  (midRoundState gen ds k).instances.length = ds.instances.length := by
  simp [midRoundState, steppedPrefix, pendingSuffix]
  omega

-- Instances before the frontier in midRoundState are stepped versions of originals
lemma midRoundState_before_frontier
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k i : ℕ)
  (hi : i < k)
  (hk : k ≤ ds.instances.length) :
  (midRoundState gen ds k).instances[i]? =
    (ds.instances[i]?).map (·.bind (step gen)) := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  rw [List.getElem?_append]
  simp only [List.length_map, List.length_take]
  rw [if_pos (by omega)]
  rw [List.getElem?_map]
  simp [List.getElem?_take]
  simp [hi]

-- Instances from the frontier onwards are unchanged
lemma midRoundState_from_frontier
  (gen : Generator Γw Γo Q)
  (ds : DovetailState (Γw := Γw) (Γo := Γo) (Q := Q))
  (k i : ℕ)
  (hi : k ≤ i) :
  (midRoundState gen ds k).instances[i]? =
    ds.instances[i]? := by
  simp only [midRoundState, steppedPrefix, pendingSuffix]
  have : (List.map (·.bind (step gen)) (ds.instances.take k) ++
          ds.instances.drop k)[i]? = ds.instances[i]? := by
    conv_rhs => rw [← List.take_append_drop k ds.instances]
    simp only [List.getElem?_append, List.length_map, List.length_take]
    rw [if_neg (by omega)]
    simp [List.getElem?_drop]
    omega
  exact this

lemma instances_length_after_steps
  (gen : Generator Γw Γo Q) (n : ℕ) :
  ((dovetailStep gen)^[n] initDovetailState).instances.length = n := by
  induction n with
  | zero => simp [initDovetailState]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp [ih]

lemma nextInput_after_steps (gen : Generator Γw Γo Q) (n : ℕ) :
    ((dovetailStep gen)^[n] initDovetailState).nextInput = n := by
  induction n with
  | zero => simp [initDovetailState]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp [ih]

lemma instance_config_after_steps
  (gen : Generator Γw Γo Q)
  (n i : ℕ) (hi : i < n) :
  ((dovetailStep gen)^[n] initDovetailState).instances[i]? =
    some (stepN gen (some (initConfig gen i.testBit)) (n - i - 1)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, dovetailStep]
    simp only [List.getElem?_append]
    by_cases hi' : i < n
    · have ih' := ih hi'
      simp only [List.length_map]
      rw [if_pos (by
        rw [instances_length_after_steps]
        exact hi')]
      rw [List.getElem?_map, ih']
      simp only [Option.map_some]
      rw [← stepN_succ]
      congr 2
      omega
    · have hi'' : i = n := by omega
      subst hi''
      simp only [List.length_map]
      rw [instances_length_after_steps, if_neg (by omega)]
      rw [show i - i = 0 by omega]
      simp only [List.length_cons, List.length_nil, zero_add,
        zero_lt_one, getElem?_pos, List.getElem_cons_zero,
    add_tsub_cancel_left, tsub_self, stepN_zero, Option.some.injEq]
      rw [nextInput_after_steps]

theorem DovetailRecognises_iff_Computes
  (gen : Generator Γw Γo Q)
  (w : List Γo) :
  DovetailRecognises gen w ↔
  ∃ input : ℕ → Bool, Computes gen (initConfig gen input) w := by
  constructor
  · -- Forward: DovetailRecognises → ∃ input, Computes
    intro ⟨n, i, cfg, h_inst, h_halt, h_out⟩
    refine ⟨Nat.testBit i, h_out ▸ ?_⟩
    have hi : i < n := by
      have hlen := instances_length_after_steps gen n
      have hdom := of_getElem?_eq_some h_inst
      simp only [hlen] at hdom
      exact hdom
    have h_stepN := instance_config_after_steps gen n i hi
    rw [h_inst] at h_stepN
    have h_eq : stepN gen (some (initConfig gen (Nat.testBit i))) (n - i - 1) = some cfg :=
      Option.some_inj.mp h_stepN.symm
    rw [stepN_eq_Steps] at h_eq
    exact Reachable.computes ⟨_, h_eq⟩ h_halt
  · -- Backward: ∃ m, Computes → DovetailRecognises
    intro ⟨f, h_computes⟩
    obtain ⟨m, h_computes'⟩ := h_computes.exists_natTestBit
    obtain ⟨k, haltCfg, h_stepN, h_halt, h_out⟩ := h_computes'.to_stepN
    refine ⟨m + k + 1, m, haltCfg, ?_, h_halt, h_out⟩
    have hm : m < m + k + 1 := by omega
    have h_inst := instance_config_after_steps gen (m + k + 1) m hm
    rw [show m + k + 1 - m - 1 = k by omega] at h_inst
    rw [h_stepN] at h_inst
    exact h_inst

variable [Inhabited Γw] [FinEnum Q]

inductive DovetailStack : Type u
  | target        -- String in Γo to be recognised. Only one copy (not one per generator instance)
  | counter       -- Booleans representing the counter that should be used for the next generator
                  --   instance. Initially empty (which corresponds to a bitstream of all zeros).
  | input         -- The bitstream prefix for each generator instance, with "none" used after the
                  --   bitstream for a given instance. If the bitstream for an instance is empty
                  --   this means that the instance will read zeros forevermore.
  | state         -- A series of Q elements, one per active instance.
  | workL         -- A none-separated series of Γw elements representing what lies to the left
                  --   of the tape head for each instance.
  | workR         -- Similar but for what is to the right of the tape head for each instance.
  | output        -- A non-separated series of Γo elements indicating what has been ouptut by each
                  --   instance.
  | saveTarget
  | saveCounter
  | saveInput
  | saveState
  | saveWorkL
  | saveWorkR
  | saveOutput

deriving instance DecidableEq for DovetailStack
deriving instance Fintype for DovetailStack
deriving instance Inhabited for DovetailStack

def stackAlphabet (Γw Γo Q : Type u)
    [Fintype Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    DovetailStack → Type u
  -- target holds Γo elements (no separator needed, it's a single word)
  | DovetailStack.target    => Γo
  -- counter holds Bool (the binary representation of the next input number)
  | DovetailStack.counter   => ULift.{u} Bool
  -- input holds Option Bool: some b for a bit, none as separator between instances
  | DovetailStack.input     => Option (ULift.{u} Bool)
  -- state holds Q, one per instance
  | DovetailStack.state     => Q
  -- workL and workR hold Option Γw: some x for a tape symbol, none as separator
  | DovetailStack.workL     => Option Γw
  | DovetailStack.workR     => Option Γw
  -- output holds Option Γo: some x for an output symbol, none as separator
  | DovetailStack.output    => Option Γo
  -- save stacks mirror their corresponding main stacks
  | DovetailStack.saveTarget  => Γo
  | DovetailStack.saveCounter => ULift.{u} Bool
  | DovetailStack.saveInput   => Option (ULift.{u} Bool)
  | DovetailStack.saveState   => Q
  | DovetailStack.saveWorkL   => Option Γw
  | DovetailStack.saveWorkR   => Option Γw
  | DovetailStack.saveOutput  => Option Γo

-- Labels correspond to the subroutines and their internal loops
inductive DovetailLabel : Type u
  | pushNewConfig_copy_counter
  | pushNewConfig_restore_counter
  | stepAll
  | stepOne
  | stepOne_workR
  | applyTransition
  | applyInputDir
  | applyWorkDir
  | checkOutput
  | saveSegment
  | saveSegment_input
  | saveSegment_workL
  | saveSegment_workR
  | saveSegment_output
  | restoreTarget
  | restoreOutput
  | restoreAll_state
  | restoreAll_input
  | restoreAll_workL
  | restoreAll_workR
  | restoreAll_output
  | incrementCounter
  | incrementCounter_loop
  | incrementCounter_restore
deriving DecidableEq, Fintype

set_option linter.style.whitespace false
set_option linter.style.longLine false
structure DovetailSigma (Γw Γo Q : Type u)
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] where

  -- ── Generator transition results ──────────────────────────────────────
  -- Populated by applyDelta, consumed by applyTransition and applyWorkDir
  transQ    : Option Q              -- new state (none = halted/spinning)
  transW    : Option Γw             -- symbol to write back to workR
  transIDir : InputTapeDirection    -- input tape direction
  transWDir : WorkTapeDirection     -- work tape direction
  transOut  : Option (Option Γo)    -- none = no output, some o = emit o
  transHalted : Bool                -- did gen.δ return none?

  -- ── Current input bit ─────────────────────────────────────────────────
  -- Populated by stepOne
  inputBit  : ULift.{u} Bool            -- the actual bit value (false if none)

  -- ── Scratch space for peek/pop decisions ──────────────────────────────
  -- Each field is dedicated to one subroutine to avoid aliasing
  peekQ     : Option Q                       -- stepAll, restoreAll_state
  peekBit   : Option (ULift.{u} Bool)            -- pushNewConfig_copy/restore, incrementCounter
  peekInput : Option (Option (ULift.{u} Bool))   -- stepOne, saveSegment_input, restoreAll_input
  peekWorkL : Option (Option Γw)             -- applyWorkDir (L), saveSegment_workL, restoreAll_workL
  peekWorkR : Option (Option Γw)             -- stepOne_workR, applyWorkDir (R), saveSegment_workR, restoreAll_workR
  peekOut   : Option (Option Γo)             -- saveSegment_output, restoreAll_output, restoreOutput
  peekTarget : Option Γo                     -- checkOutput, restoreTarget

  -- ── Binary counter ────────────────────────────────────────────────────
  carry     : Option (ULift.{u} Bool)   -- incrementCounter carry bit
set_option linter.style.whitespace true
set_option linter.style.longLine true

instance : Inhabited DovetailLabel := ⟨DovetailLabel.pushNewConfig_copy_counter⟩

instance : Inhabited (DovetailSigma Γw Γo Q) :=
  ⟨{ transQ      := none
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
     carry       := none }⟩

instance : Fintype (ULift.{u} Bool) :=
  Fintype.ofEquiv Bool ⟨ULift.up, ULift.down, fun _ => rfl, fun _ => rfl⟩

instance : DecidableEq (ULift.{u} Bool) :=
  fun a b => decidable_of_iff (a.down = b.down) (by cases a; cases b; simp [ULift.ext_iff])

instance [Fintype Γw] [Fintype Γo] [Fintype Q] [DecidableEq Γw] [DecidableEq Γo] [DecidableEq Q] :
    Fintype (DovetailSigma Γw Γo Q) :=
  Fintype.ofEquiv
    (Option Q × Option Γw × InputTapeDirection × WorkTapeDirection ×
     Option (Option Γo) × Bool × ULift.{u} Bool × Option Q ×
     Option (ULift.{u} Bool) × Option (Option (ULift.{u} Bool)) ×
     Option (Option Γw) × Option (Option Γw) ×
     Option (Option Γo) × Option Γo × Option (ULift.{u} Bool))
    { toFun := fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ =>
        { transQ := a, transW := b, transIDir := c, transWDir := d,
          transOut := e, transHalted := f, inputBit := g, peekQ := h,
          peekBit := i, peekInput := j, peekWorkL := k, peekWorkR := l,
          peekOut := m, peekTarget := n, carry := o }
      invFun := fun σ =>
        (σ.transQ, σ.transW, σ.transIDir, σ.transWDir,
         σ.transOut, σ.transHalted, σ.inputBit, σ.peekQ,
         σ.peekBit, σ.peekInput, σ.peekWorkL, σ.peekWorkR,
         σ.peekOut, σ.peekTarget, σ.carry)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

def dovetailInit {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (target : List Γo) :
    Turing.TM2.Cfg (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.init DovetailStack.target target

/-
Definitions of transitions
-/

def pushNewConfig_copy_counter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_restore_counter) )
    ( Turing.TM2.Stmt.pop DovetailStack.counter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.saveCounter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| -- Copy counter to save_counter
         Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_copy_counter) )

-- Restoring save_counter to counter + input
def pushNewConfig_restore_counter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter
    (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.state (fun _ => gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter
        (fun σ b => { σ with peekBit := b })
      <| Turing.TM2.Stmt.push DovetailStack.counter
        (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekBit)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_restore_counter) )

-- step all remaining generator configurations
def stepAll {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.state (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( -- state stack empty, all instances processed
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_state) )
    ( -- state stack non-empty: pop the state and process next instance
      Turing.TM2.Stmt.pop DovetailStack.state (fun σ s => { σ with transQ := s })
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepOne) )

def applyDelta {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (σ : DovetailSigma Γw Γo Q) : DovetailSigma Γw Γo Q :=
  match σ.transW with
  | some w =>
      match gen.δ (σ.transQ.getD gen.init) σ.inputBit.down w with
      -- getD gen.init is unreachable: transQ is always some q at this point
      | none =>
          -- halted: leave transQ, transW, directions all unchanged
          -- the instance will spin in this configuration forever
          { σ with
            transIDir   := InputTapeDirection.N
            transWDir   := WorkTapeDirection.N
            transOut    := none
            transHalted := true }
      | some (q', w', o, id, wd) =>
          { σ with
            transQ      := some q'
            transW      := some w'
            transOut    := some o
            transIDir   := id
            transWDir   := wd
            transHalted := false }
  | none => σ  -- unreachable: transW is always some w at this point

def applyTransition {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => σ.transHalted)
    ( -- instance halted: push state back before checking output
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkOutput) )
    ( -- instance still running: push new state
      Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.transQ.getD gen.init)
      -- push written symbol to workR
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.transW.map some |>.getD none)
      -- handle output symbol
      <| Turing.TM2.Stmt.branch (fun σ => match σ.transOut with
          | some (some _) => true
          | _             => false)
        ( Turing.TM2.Stmt.push DovetailStack.output
            (fun σ => match σ.transOut with
              | some o => o
              | none   => none)  -- unreachable
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyInputDir) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyInputDir) ) )

def applyInputDir {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  -- pop input bit only if direction is R and the bit is real
  Turing.TM2.Stmt.branch (fun σ => match σ.transIDir, σ.peekInput with
      | InputTapeDirection.R, some (some _) => true
      | _, _                                => false)
    ( -- direction is R and real bit present: pop it
      Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyWorkDir) )
    ( -- direction is N or no real bit: leave input stack unchanged
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyWorkDir) )

-- step one generator configuration
def stepOne {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  -- peek input: set inputBit for use by applyDelta
  -- real bits will be popped later, conditionally on transIDir = R
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with
    inputBit  := match i with
                 | some (some b) => b
                 | _             => ULift.up false
    peekInput := i })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepOne_workR)

-- peek workR, pop if real symbol, then apply δ
def stepOne_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with
    transW    := match w with
                 | some (some x) => some x
                 | _             => some gen.blank
    peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
      | some (some _) => true
      | _             => false)
    ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyTransition) )
    ( Turing.TM2.Stmt.load (fun σ => applyDelta gen σ)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.applyTransition) )

def applyWorkDir {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.branch (fun σ => match σ.transWDir with
      | WorkTapeDirection.L => true
      | _                   => false)
    ( -- move left: pop top of workL (or blank), push to workR
      Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with
        peekWorkL := w })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some (some _) => true
          | _             => false)
        ( Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
          <| Turing.TM2.Stmt.push DovetailStack.workR
            (fun σ => match σ.peekWorkL with
              | some (some x) => some x
              | _             => some gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
        ( Turing.TM2.Stmt.push DovetailStack.workR
            (fun _ => some gen.blank)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )
    ( Turing.TM2.Stmt.branch (fun σ => match σ.transWDir with
        | WorkTapeDirection.R => true
        | _                   => false)
      ( -- move right: pop top of workR (or blank), push to workL
        Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with
          peekWorkR := w })
        <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
            | some (some _) => true
            | _             => false)
          ( Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
            <| Turing.TM2.Stmt.push DovetailStack.workL
              (fun σ => match σ.peekWorkR with
                | some (some x) => some x
                | _             => some gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
          ( Turing.TM2.Stmt.push DovetailStack.workL
              (fun _ => some gen.blank)
            <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )
      ( -- no move (WorkTapeDirection.N)
        Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) ) )

def checkOutput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.target (fun σ t => { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( -- target exhausted: check output also exhausted
      Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
            | none      => true   -- stack empty
            | some none => true   -- segment separator
            | _         => false)
        ( -- both exhausted: accept
          Turing.TM2.Stmt.halt )
        ( -- output longer than target: no match
          Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) ) )
    ( -- target not exhausted: peek output
      Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
            | none      => true   -- stack empty
            | some none => true   -- segment separator
            | _         => false)
        ( -- output shorter than target: no match
          Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) )
        ( -- both non-empty: compare
          Turing.TM2.Stmt.branch (fun σ => match σ.peekTarget, σ.peekOut with
              | some t, some (some o) => decide (t = o)
              | _, _                  => false)
            ( -- match: pop both, push to save stacks, loop
              Turing.TM2.Stmt.pop DovetailStack.target (fun σ _ => σ)
              <| Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
              <| Turing.TM2.Stmt.push DovetailStack.saveTarget
                (fun σ => σ.peekTarget.getD default)
              <| Turing.TM2.Stmt.push DovetailStack.saveOutput
                (fun σ => σ.peekOut.getD none)
              <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.checkOutput) )
            ( -- mismatch: no match
              Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) ) ) )

def restoreTarget {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveTarget (fun σ t => { σ with peekTarget := t })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekTarget.isNone)
    ( -- saveTarget exhausted: now restore saveOutput back to output
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreOutput) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveTarget (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.target
        (fun σ => σ.peekTarget.getD default)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreTarget) )

def restoreOutput {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( -- saveOutput exhausted: proceed to saveSegment
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreOutput) )

def saveSegment {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  -- pop state and push to saveState
  Turing.TM2.Stmt.pop DovetailStack.state (fun σ q => { σ with peekQ := q })
  <| Turing.TM2.Stmt.push DovetailStack.saveState
    (fun σ => σ.peekQ.getD gen.init)  -- getD gen.init unreachable
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_input)

-- Move input segment to saveInput, including the none delimiter
def saveSegment_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.input (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( -- stack empty (oldest instance, no delimiter): proceed
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) )
    ( -- some value on top: pop and push to saveInput
      Turing.TM2.Stmt.pop DovetailStack.input (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveInput
        (fun σ => σ.peekInput.getD none)
      -- if it was the none delimiter, stop; otherwise continue
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekInput with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_input) ) )

-- Move workL segment to saveWorkL, including the none delimiter
def saveSegment_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( -- stack empty (oldest instance, no delimiter): proceed
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) )
    ( -- some value on top: pop and push to saveWorkL
      Turing.TM2.Stmt.pop DovetailStack.workL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkL
        (fun σ => σ.peekWorkL.getD none)
      -- if it was the none delimiter, stop; otherwise continue
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkL with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workL) ) )

-- Move workR segment to saveWorkR, including the none delimiter
def saveSegment_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.workR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( -- stack empty (oldest instance, no delimiter): proceed
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) )
    ( -- some value on top: pop and push to saveWorkR
      Turing.TM2.Stmt.pop DovetailStack.workR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveWorkR
        (fun σ => σ.peekWorkR.getD none)
      -- if it was the none delimiter, stop; otherwise continue
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekWorkR with
          | some none => true
          | _         => false)
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_workR) ) )

-- Move output segment to saveOutput, including the none delimiter
def saveSegment_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.output (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( -- stack empty (oldest instance, no delimiter): back to stepAll
      Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
    ( -- some value on top: pop and push to saveOutput
      Turing.TM2.Stmt.pop DovetailStack.output (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.saveOutput
        (fun σ => σ.peekOut.getD none)
      -- if it was the none delimiter, stop; otherwise continue
      <| Turing.TM2.Stmt.branch (fun σ => match σ.peekOut with
          | some none => true
          | _         => false)
        ( -- all segments saved: back to stepAll
          Turing.TM2.Stmt.goto (fun _ => DovetailLabel.stepAll) )
        ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.saveSegment_output) ) )

def restoreAll_state {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveState (fun σ s => { σ with peekQ := s })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekQ.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_input) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveState (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.state
        (fun σ => σ.peekQ.getD gen.init)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_state) )

def restoreAll_input {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveInput (fun σ i => { σ with peekInput := i })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekInput.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.input (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workL) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveInput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.input
        (fun σ => σ.peekInput.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_input) )

def restoreAll_workL {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkL (fun σ w => { σ with peekWorkL := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkL.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workL (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workR) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkL (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workL
        (fun σ => σ.peekWorkL.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workL) )

def restoreAll_workR {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveWorkR (fun σ w => { σ with peekWorkR := w })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekWorkR.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.workR (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_output) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveWorkR (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.workR
        (fun σ => σ.peekWorkR.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_workR) )

def restoreAll_output {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveOutput (fun σ o => { σ with peekOut := o })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekOut.isNone)
    ( Turing.TM2.Stmt.push DovetailStack.output (fun _ => none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveOutput (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.output
        (fun σ => σ.peekOut.getD none)
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.restoreAll_output) )

-- Increment the binary counter (LSB on top, no leading falses)
-- Works by propagating carry through the stack to saveCounter, then restoring
def incrementCounter {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.load (fun σ => { σ with carry := some (ULift.up true) })
  <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_loop)

-- Process one bit with carry
def incrementCounter_loop {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.counter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( -- counter empty: if carry, push true; done
      Turing.TM2.Stmt.branch (fun σ => match σ.carry with
          | some b => ULift.down b
          | none   => false)
        ( -- carry set: push true onto counter
          Turing.TM2.Stmt.push DovetailStack.counter (fun _ => ULift.up true)
          <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) )
        ( -- no carry: done, restore
          Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) ) )
    ( -- counter non-empty: pop bit, compute new bit and carry
      Turing.TM2.Stmt.pop DovetailStack.counter (fun σ _ => σ)
      <| Turing.TM2.Stmt.load (fun σ =>
          let bit      := (σ.peekBit.getD (ULift.up false)).down
          let carry    := (σ.carry.getD (ULift.up false)).down
          let newBit   := Bool.xor bit carry
          let newCarry := Bool.and bit carry
          { σ with
            peekBit := some (ULift.up newBit)
            carry   := some (ULift.up newCarry) })
      <| Turing.TM2.Stmt.push DovetailStack.saveCounter
          (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_loop) )

-- Restore saveCounter back to counter
def incrementCounter_restore {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q] :
    Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q) :=
  Turing.TM2.Stmt.peek DovetailStack.saveCounter (fun σ b => { σ with peekBit := b })
  <| Turing.TM2.Stmt.branch (fun σ => σ.peekBit.isNone)
    ( Turing.TM2.Stmt.goto (fun _ => DovetailLabel.pushNewConfig_copy_counter) )
    ( Turing.TM2.Stmt.pop DovetailStack.saveCounter (fun σ _ => σ)
      <| Turing.TM2.Stmt.push DovetailStack.counter
          (fun σ => σ.peekBit.getD (ULift.up false))
      <| Turing.TM2.Stmt.goto (fun _ => DovetailLabel.incrementCounter_restore) )

def dovetailMachine {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q) :
    DovetailLabel → Turing.TM2.Stmt (stackAlphabet Γw Γo Q) DovetailLabel (DovetailSigma Γw Γo Q)
  | DovetailLabel.pushNewConfig_copy_counter => pushNewConfig_copy_counter
  | DovetailLabel.pushNewConfig_restore_counter => pushNewConfig_restore_counter gen
  | DovetailLabel.stepAll => stepAll
  | DovetailLabel.stepOne => stepOne
  | DovetailLabel.stepOne_workR => stepOne_workR gen
  | DovetailLabel.applyTransition => applyTransition gen
  | DovetailLabel.applyInputDir => applyInputDir
  | DovetailLabel.applyWorkDir => applyWorkDir gen
  | DovetailLabel.checkOutput => checkOutput
  | DovetailLabel.restoreOutput => restoreOutput
  | DovetailLabel.restoreTarget => restoreTarget
  | DovetailLabel.saveSegment => saveSegment gen
  | DovetailLabel.saveSegment_input => saveSegment_input
  | DovetailLabel.saveSegment_workL => saveSegment_workL
  | DovetailLabel.saveSegment_workR => saveSegment_workR
  | DovetailLabel.saveSegment_output => saveSegment_output
  | DovetailLabel.incrementCounter => incrementCounter
  | DovetailLabel.incrementCounter_loop => incrementCounter_loop
  | DovetailLabel.incrementCounter_restore => incrementCounter_restore
  | DovetailLabel.restoreAll_output => restoreAll_output
  | DovetailLabel.restoreAll_workR => restoreAll_workR
  | DovetailLabel.restoreAll_workL => restoreAll_workL
  | DovetailLabel.restoreAll_input => restoreAll_input
  | DovetailLabel.restoreAll_state => restoreAll_state gen

-- The simulation relation
-- def DovetailTrCfg (ds : DovetailState) (cfg : TM2.Cfg ...) : Prop := sorry

-- The key simulation lemma
-- lemma dovetail_simulates :
--     Respects (dovetailMachineStep) (TM2.step (dovetailMachine gen)) DovetailTrCfg := sorry

-- The chain to TM0 recognisability
-- lemma generable_subset_tm0_recognisable :
--     generableLanguages ⊆ languagesRecognisedByTM0s := sorry

end Dovetailing

-- The dovetail TM2 halts on input `target` iff `target` is in the generated language.
theorem dovetailMachine_recognises {Γw Γo Q : Type u}
    [FinEnum Γw] [Inhabited Γw] [Inhabited Γo] [FinEnum Γo] [FinEnum Q]
    (gen : Generator Γw Γo Q)
    (target : List Γo) :
    (Turing.TM2.eval (dovetailMachine gen) DovetailStack.target target.reverse).Dom ↔
    target ∈ generatedLanguage gen Finset.univ (generator_supports_univ gen) := by
  sorry

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
        pushNewConfig_copy_counter, pushNewConfig_restore_counter,
        stepAll, stepOne, stepOne_workR, applyTransition, applyInputDir,
        applyWorkDir, checkOutput, restoreTarget, restoreOutput,
        saveSegment, saveSegment_input, saveSegment_workL, saveSegment_workR,
        saveSegment_output, restoreAll_state, restoreAll_input,
        restoreAll_workL, restoreAll_workR, restoreAll_output,
        incrementCounter, incrementCounter_loop, incrementCounter_restore,
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
