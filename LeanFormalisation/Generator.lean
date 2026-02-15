import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import LeanFormalisation.Encoding

namespace RandomisedGeneration

inductive WorkTapeDirection
  | L     -- move left
  | R     -- move right
  | N     -- stay / no move

instance : Coe WorkTapeDirection ℤ :=
⟨fun
  | WorkTapeDirection.L => -1
  | WorkTapeDirection.N => 0
  | WorkTapeDirection.R => 1⟩

inductive InputTapeDirection
  | R     -- move right
  | N     -- stay / no move

instance : Coe InputTapeDirection ℕ :=
⟨fun
  | InputTapeDirection.N => 0
  | InputTapeDirection.R => 1⟩

-- Sigma is the working tape alphabet.
-- Γ is the output tape alphabet.
-- Q is the set of states.
structure Generator (Γw Γo Q : Type u)
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
where
  init : Q -- Initial state
  blank : Γw -- Blank symbol for the working tape
  -- A transition is determined by:
  -- - the current state
  -- - a boolean from the input tape
  -- - a symbol from the working tape
  -- A transition yields none if it causes the machine to halt.
  -- Otherwise it yields:
  -- - A new state
  -- - A symbol to be written to the working tape
  -- - Optionally a symbol to be written to the output tape
  -- - A value indicating whether the input tape head should move
  -- - A value indicating the direction in which the working tape head should move
  δ : Q -> Bool -> Γw → Option (Q × Γw × Option Γo × InputTapeDirection × WorkTapeDirection)
  -- Constraint: outputs never contain the default symbol
  no_default_output : ∀ q b w q' w' o itd wtd,
    δ q b w = some (q', w', o, itd, wtd) →
    ∀ γ, o = some γ → γ ≠ default

@[ext]
structure GeneratorConfig (Γw Γo Q : Type u)
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
where
  (state : Q)
  (input : ℕ → Bool)
  (inputIndex : ℕ)
  (work : ℤ → Γw)
  (workIndex : ℤ)
  (output : List Γo)

def step {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) (cfg : GeneratorConfig Γw Γo Q) :
  Option (GeneratorConfig Γw Γo Q) :=
match gen.δ cfg.state (cfg.input cfg.inputIndex) (cfg.work cfg.workIndex) with
  | none => none
  | some (q', w', out?, inDir, workDir) =>
    some {
      state := q',
      input := cfg.input,
      inputIndex := cfg.inputIndex + inDir,
      work := fun x => if (x = cfg.workIndex) then w' else cfg.work x,
      workIndex := cfg.workIndex + workDir,
      output :=
        match out? with
        | none => cfg.output
        | some g => cfg.output ++ [g]
    }

def initConfig {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) (input : ℕ → Bool) :
  GeneratorConfig Γw Γo Q :=
{ state := gen.init
  input := input
  inputIndex := 0
  work := fun _ => gen.blank
  workIndex := 0
  output := []
}

def haltingConfig {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  (cfg : GeneratorConfig Γw Γo Q) : Prop :=
step gen cfg = none

inductive Computes {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : GeneratorConfig Γw Γo Q → List Γo → Prop
  | halt (cfg : GeneratorConfig Γw Γo Q) :
      step gen cfg = none → Computes gen cfg cfg.output
  | step (cfg cfg' : GeneratorConfig Γw Γo Q) (out : List Γo) :
      step gen cfg = some cfg' → Computes gen cfg' out → Computes gen cfg out

inductive Steps {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) :
  GeneratorConfig Γw Γo Q →
  GeneratorConfig Γw Γo Q →
  ℕ → Prop
| refl (cfg) :
    Steps gen cfg cfg 0
| step (cfg cfg' cfg'' n) :
    step gen cfg = some cfg' →
    Steps gen cfg' cfg'' n →
    Steps gen cfg cfg'' (n + 1)

lemma Steps.trans {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  {gen : Generator Γw Γo Q} {cfg1 cfg2 cfg3 : GeneratorConfig Γw Γo Q} {n m : ℕ} :
  Steps gen cfg1 cfg2 n → Steps gen cfg2 cfg3 m → Steps gen cfg1 cfg3 (n + m) := by
  intro h1 h2
  induction h1 with
  | refl =>
    rw [zero_add]
    exact h2
  | step cfg cfg' cfg'' n h_step h_steps ih =>
    have : n + 1 + m = n + m + 1 := by omega
    rw [this]
    apply Steps.step cfg cfg' cfg3 (n + m) h_step
    exact ih h2

def StepsTo {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q)
(cfg : GeneratorConfig Γw Γo Q)
(cfg' : GeneratorConfig Γw Γo Q) : Prop :=
  ∃ n, Steps gen cfg cfg' n

lemma StepsTo.refl {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg : GeneratorConfig Γw Γo Q} :
  StepsTo gen cfg cfg :=
by
  unfold StepsTo
  refine ⟨0, ?_⟩
  exact Steps.refl cfg

lemma StepsTo.trans {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg1 cfg2 cfg3 : GeneratorConfig Γw Γo Q} :
  StepsTo gen cfg1 cfg2 → StepsTo gen cfg2 cfg3 → StepsTo gen cfg1 cfg3 :=
by
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  exact ⟨n + m, Steps.trans h1 h2⟩

def HaltsFrom {Γw Γo Q}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q)
(cfg : GeneratorConfig Γw Γo Q) : Prop :=
  ∃ cfg' n,
    Steps gen cfg cfg' n ∧
    haltingConfig gen cfg'

lemma StepsTo.computes {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  {gen : Generator Γw Γo Q} {cfg haltCfg : GeneratorConfig Γw Γo Q} :
  StepsTo gen cfg haltCfg → step gen haltCfg = none →
  Computes gen cfg haltCfg.output := by
  intro ⟨n, h_steps⟩ h_halt
  induction h_steps with
  | refl cfg =>
    exact Computes.halt cfg h_halt
  | step cfg cfg' cfg'' n h_step h_steps' ih =>
    apply Computes.step cfg cfg' cfg''.output h_step
    exact ih h_halt

-- This captures the idea of a generator not being able to loop forever without
-- consuming an input bit.
def InputProgressing {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : Prop :=
∀ cfg, ∃ cfg' n,
  Steps gen cfg cfg' n ∧ (haltingConfig gen cfg' ∨ cfg'.inputIndex > cfg.inputIndex)

lemma step_preserves_no_default {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q) (cfg cfg' : GeneratorConfig Γw Γo Q) :
  step gen cfg = some cfg' →
  default ∉ cfg.output →
  default ∉ cfg'.output := by
  intro h_step h_no_default
  unfold step at h_step
  split at h_step
  · contradiction
  · rename_i q' w' out? inDir workDir h_δ
    injection h_step with h_eq
    rw [← h_eq]
    simp only
    intro h
    cases out? with
    | none =>
      exact h_no_default h
    | some γ =>
      simp only [List.mem_append, List.mem_singleton] at h
      cases h with
      | inl h_old => exact h_no_default h_old
      | inr h_new =>
        have : γ ≠ default := gen.no_default_output _ _ _ _ _ _ _ _ h_δ γ rfl
        exact this h_new.symm

lemma Computes_no_default {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
  (gen : Generator Γw Γo Q) (cfg : GeneratorConfig Γw Γo Q) (out : List Γo) :
  Computes gen cfg out →
  default ∉ cfg.output →
  default ∉ out := by
  intro h_comp h_no_default
  induction h_comp with
  | halt cfg h_halt =>
    exact h_no_default
  | step cfg cfg' out h_step h_comp' ih =>
    apply ih
    exact step_preserves_no_default gen cfg cfg' h_step h_no_default

def Language (Γ : Type u)
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
 : Type u :=
  { L : Set (List Γ) // ∀ input ∈ L, default ∉ input }

def generated_language {Γw Γo Q : Type u}
[Fintype Γw]
[Inhabited Γo] [Fintype Γo] [FinEnum Γo] [DecidableEq Γo]
[Fintype Q]
(gen : Generator Γw Γo Q) : Language Γo :=
  ⟨{ out | ∃ input, Computes gen (initConfig gen input) out },
   fun out ⟨input, h_comp⟩ =>
     Computes_no_default gen (initConfig gen input) out h_comp (by simp [initConfig])⟩

def generable_languages {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ] : Set (Language Γ) :=
{ L | ∃ (Γw Q : Type u) (_ : Fintype Γw) (_ : Fintype Q)
  (gen : Generator Γw Γ Q), generated_language gen = L }

def TM0_language {Γ Λ : Type u}
[Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) : Language Γ :=
  ⟨{ input | default ∉ input ∧ (Turing.TM0.eval M input).Dom },
   fun _ hInput => hInput.1⟩

def TM0_recognisable_languages (Γ : Type u)
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
: Set (Language Γ) :=
  { L | ∃ (Λ : Type u) (_ : Inhabited Λ) (_ : Fintype Λ) (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)),
    L = TM0_language M }

namespace GenerationByTM0Simulation

structure LoadState (Γ : Type u) (enc : Encoding Γ) where
  bitsRead : Fin (enc.W + 1)      -- 0 .. W
  acc      : Fin (2 ^ enc.W)      -- fixed width accumulator
  accBound : acc.val ≤ 2 ^ bitsRead.val - 1 -- invariant
deriving Fintype

inductive GenState (Λ Γ : Type u)
[Fintype Λ]
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (enc : Encoding Γ) where
  | load (ls : LoadState Γ enc)
  | rewind
  | sim  (q  : Λ)
deriving Fintype

def TM_generator {Γ Λ : Type u}
[Inhabited Λ] [Fintype Λ]
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  {enc : Encoding Γ}
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  : Generator (Γw := Γ) (Γo := Γ) (Q := GenState Λ Γ enc) :=
  {
    init := GenState.load {bitsRead := 0, acc := 0, accBound := by simp},
    blank := (default : Γ),
    δ := fun state b (w : Γ) =>
      match state with
      | GenState.load ls =>
        if h_eq : ls.bitsRead.val = enc.W then
          -- done reading, produce a symbol
          match enc.enum ls.acc with
          | none =>
            -- An invalid encoding has been found; this indicates end of input.
            -- Switch to rewind mode (already going back one)
            some (
              GenState.rewind,
              w,
              none,
              InputTapeDirection.N,
              WorkTapeDirection.L
            )
          | some (g : Γ) =>
            if g = default then
              -- Default symbol decoded; switch to rewind mode
              some (
                GenState.rewind,
                w,
                none,
                InputTapeDirection.N,
                WorkTapeDirection.L
              )
            else
              -- A non-default symbol has been fully decoded. Write it to the work tape
              -- and produce it as an output. Reset the load state to start
              -- on the next symbol.
              some (
                GenState.load { bitsRead := 0, acc := 0, accBound := by simp},
                g,
                g,
                InputTapeDirection.N,
                WorkTapeDirection.R
              )
        else
          let newBits : Fin (enc.W + 1) := ⟨ls.bitsRead.val + 1, by omega⟩
          --
          have h_bit : 2 * ls.acc.val + (if b then 1 else 0) ≤ 2 * 2 ^ ls.bitsRead.val - 1 := by
            have : 2 * ls.acc.val ≤ 2 * 2 ^ ls.bitsRead.val - 2 := by
              calc 2 * ls.acc.val
                  ≤ 2 * (2 ^ ls.bitsRead.val - 1) := by simp [ls.accBound]
                _ = 2 * 2 ^ ls.bitsRead.val - 2 := by simp [Nat.mul_sub_left_distrib]
            have : (if b then 1 else 0) ≤ 1 := by split_ifs <;> omega
            have : 1 ≤ 2 ^ ls.bitsRead.val := Nat.one_le_pow _ _ (by norm_num)
            omega
          --
          have h_newAcc_bound : 2 * ls.acc.val + (if b then 1 else 0) < 2 ^ enc.W := by
            have h_bitsRead_lt_W : ls.bitsRead.val < enc.W := by omega
            have : 2 ^ (ls.bitsRead.val + 1) ≤ 2 ^ enc.W :=
              Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h_bitsRead_lt_W)
            have : 2 * 2 ^ ls.bitsRead.val = 2 ^ (ls.bitsRead.val + 1) := by ring
            omega
          --
          let newAcc : Fin (2^enc.W) := ⟨2 * ls.acc.val + if b then 1 else 0, h_newAcc_bound⟩
          --
          have h_accBound : newAcc.val ≤ 2 ^ newBits.val - 1 := by
            simp only [newAcc, newBits, pow_succ]
            convert h_bit using 2; ring
          some (
            GenState.load { bitsRead := newBits, acc := newAcc, accBound := h_accBound },
            w,
            none,
            InputTapeDirection.R,
            WorkTapeDirection.N
          )
      | GenState.rewind =>
        if (w = (default : Γ)) then
          -- We have fully rewound, so proceed to simulation
          some (
            GenState.sim (default : Λ),
            w,
            none,
            InputTapeDirection.N,
            WorkTapeDirection.R
          )
        else
          -- Not rewound far enough
          some (
            GenState.rewind,
            w,
            none,
            InputTapeDirection.N,
            WorkTapeDirection.L
          )
      | GenState.sim q =>
        match M q w with
        | none => none
        | some (q', stmt) =>
          match stmt with
          | Turing.TM0.Stmt.write (g : Γ) =>
            some (GenState.sim q', g, none, InputTapeDirection.N, WorkTapeDirection.N)
          | Turing.TM0.Stmt.move Turing.Dir.left =>
            some (GenState.sim q', w, none, InputTapeDirection.N, WorkTapeDirection.L)
          | Turing.TM0.Stmt.move Turing.Dir.right =>
            some (GenState.sim q', w, none, InputTapeDirection.N, WorkTapeDirection.R),
    no_default_output := by
      intros q b w q' w' o itd wtd h_δ γ h_o
      cases q with
      | load ls =>
        simp only at h_δ
        split at h_δ
        · -- bitsRead.val = enc.W
          split at h_δ
          · -- enc.enum ls.acc = none
            simp only [Option.some.injEq] at h_δ
            obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
            simp at h_o
          · -- enc.enum ls.acc = some g
            rename_i g
            split at h_δ
            · -- g = default
              simp only [Option.some.injEq] at h_δ
              obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
              simp at h_o
            · -- g ≠ default
              rename_i h_ne
              simp only [Option.some.injEq] at h_δ
              obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
              simp only [Option.some.injEq] at h_o
              rw [← h_o]
              exact h_ne
        · -- bitsRead.val ≠ enc.W
          simp only [Option.some.injEq] at h_δ
          obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
          simp at h_o
      | rewind =>
        simp only at h_δ
        split at h_δ <;> simp_all
      | sim q_tm =>
        simp only at h_δ
        split at h_δ
        · contradiction
        · rename_i q'_tm stmt heq_M
          cases stmt
          · -- move case
            rename_i dir
            cases dir
            · -- left
              simp only [Option.some.injEq] at h_δ
              obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
              simp at h_o
            · -- right
              simp only [Option.some.injEq] at h_δ
              obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
              simp at h_o
          · -- write case
            simp only [Option.some.injEq] at h_δ
            obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
            simp at h_o
}

def DecodeBitInv {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  {k : ℕ} (hk : k ≤ input.length)
  (x : Fin (WIDTH Γ + 1))
  : Prop :=
cfg.state = GenState.load {
  bitsRead := x,
  acc := readBlockOfBitsW (bitstreamFromInput input) ((WIDTH Γ) * k) x (WIDTH Γ) (by omega)
  accBound := by
    have h := readBlockOfBits_lt_pow (bitstreamFromInput input) ((WIDTH Γ) * k) x.val
    exact Nat.le_pred_of_lt h
}
∧ cfg.inputIndex = k * (StandardEncoding Γ).W + x.val
∧ cfg.workIndex = k
∧ (∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
∧ cfg.input = bitstreamFromInput input
∧ cfg.output = input.take k

def DecodeSymbolInv {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  {k : ℕ} (hk : k ≤ input.length)
   : Prop :=
  cfg.state = GenState.load  {
    bitsRead := 0,
    acc := 0,
    accBound := by simp }
  ∧ cfg.inputIndex = k * (StandardEncoding Γ).W
  ∧ cfg.workIndex = k
  ∧ (∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
  ∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  ∧ cfg.input = bitstreamFromInput input
  ∧ cfg.output = input.take k

lemma decodeBitWithinSymbol {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  {k : ℕ} (hk : k ≤ input.length)
  (x : Fin (WIDTH Γ))
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (hinv : DecodeBitInv input cfg (k := k) (by omega) ⟨x, Nat.lt_succ_of_lt x.isLt⟩) :
  ∃ cfg',
    step (TM_generator (enc := StandardEncoding Γ) M) cfg = some cfg' ∧
    DecodeBitInv input cfg' (k := k) (by omega) ⟨x.val + 1, by omega⟩ := by
  obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩ := hinv
  -- Simplify step to get concrete configuration
  simp only [step, TM_generator]
  rw [h_state, h_input, h_inputIndex, h_workIndex]
  have h_not_done : x.val ≠ (StandardEncoding Γ).W := ne_of_lt x.isLt
  simp only [h_not_done, ↓reduceDIte]
  -- Now the goal should be ∃ cfg', some ⟨...⟩ = some cfg' ∧ ...
  -- We can use the configuration that appears in the some
  use {
    state := GenState.load {
      bitsRead := ⟨x.val + 1, Nat.add_lt_add_right x.isLt 1⟩,
      acc := ⟨2 * (readBlockOfBitsW (bitstreamFromInput input) (WIDTH Γ * k) x.val (WIDTH Γ)
        (by omega)).val + (if cfg.input (cfg.inputIndex) then 1 else 0),
      by
        -- Goal: prove < 2^(WIDTH Γ)
        have h_acc_lt : (readBlockOfBitsW (bitstreamFromInput input)
          (WIDTH Γ * k) x.val (WIDTH Γ) (by omega)).val < 2^x.val := by
          exact readBlockOfBits_lt_pow (bitstreamFromInput input) (WIDTH Γ * k) x.val
        have h_bit : (if cfg.input cfg.inputIndex then 1 else 0) ≤ 1 := by split_ifs <;> omega
        have : x.val < WIDTH Γ := x.isLt
        calc 2 * (readBlockOfBitsW (bitstreamFromInput input)
          (WIDTH Γ * k) x.val (WIDTH Γ) (by omega)).val +
                (if cfg.input cfg.inputIndex then 1 else 0)
            ≤ 2 * (2^x.val - 1) + 1 := by
              have h_acc_lt := readBlockOfBits_lt_pow (bitstreamFromInput input) (WIDTH Γ * k) x.val
              have h_bit : (if cfg.input cfg.inputIndex then 1 else 0) ≤ 1 := by split_ifs <;> omega
              omega
          _ = 2^(x.val + 1) - 1 := by
              have : 2^(x.val + 1) = 2 * 2^x.val := by rw [pow_succ]; ring
              omega
          _ < 2^(x.val + 1) := by omega
          _ ≤ 2^(WIDTH Γ) := by
              apply Nat.pow_le_pow_right <;> omega
      ⟩,
      accBound := by
        -- Goal: prove acc.val ≤ 2^(x+1) - 1
        simp only
        calc 2 * (readBlockOfBitsW (bitstreamFromInput input)
              (WIDTH Γ * k) x.val (WIDTH Γ) (by omega)).val +
            (if cfg.input cfg.inputIndex then 1 else 0)
            ≤ 2 * (2^x.val - 1) + 1 := by
              have h_acc_lt := readBlockOfBits_lt_pow (bitstreamFromInput input) (WIDTH Γ * k) x.val
              have h_bit : (if cfg.input cfg.inputIndex then 1 else 0) ≤ 1 := by split_ifs <;> omega
              simp only [readBlockOfBitsW] at *
              omega
          _ = 2^(x.val + 1) - 1 := by
              have : 2^(x.val + 1) = 2 * 2^x.val := by rw [pow_succ]; ring
              have h_eq : 2^(x.val + 1) = 2 * 2^x.val := by rw [pow_succ]; ring
              rw [h_eq]
              have h_pos : 0 < 2^x.val := by positivity
              omega
    },
    input := cfg.input,
    inputIndex := cfg.inputIndex + 1,
    work := fun i => if i = cfg.workIndex then cfg.work cfg.workIndex else cfg.work i,
    workIndex := cfg.workIndex,
    output := cfg.output
  }
  constructor
  · simp only [h_input, h_inputIndex, h_workIndex]
    rfl
  constructor
  · simp only [GenState.load.injEq, LoadState.mk.injEq, true_and]
    simp only [readBlockOfBitsW, Fin.mk.injEq]
    rw [readBlockOfBitsNat_succ]
    simp
    simp [h_input, h_inputIndex, WIDTH, Nat.mul_comm]
  constructor
  · simp only [h_inputIndex]
    ring
  constructor
  · simp only [h_workIndex]
  constructor
  · intro i hi
    simp only
    split_ifs with heq
    · omega
    · exact h_work_lt i hi
  constructor
  · intro i hi
    simp only
    split_ifs with heq
    · subst heq
      apply h_work_ge
      omega
    · exact h_work_ge i hi
  constructor
  · exact h_input
  · exact h_output

lemma input_symbols_not_default {Γ : Type u}
  [Inhabited Γ]
  (input : List Γ) (h_no_default : default ∉ input)
  {k : ℕ} (hk : k < input.length) :
  input.get ⟨k, hk⟩ ≠ default := by
  intro h_eq
  apply h_no_default
  rw [← h_eq]
  exact List.get_mem input ⟨k, hk⟩

lemma writeDecodedSymbol {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  {k : ℕ} (hk : k < input.length)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (acc : Fin (2 ^ (StandardEncoding Γ).W))
  (h_state : cfg.state = GenState.load {
    bitsRead := ⟨(StandardEncoding Γ).W, by omega⟩,
    acc := acc,
    accBound := by simp; omega
  })
  (h_enum : (StandardEncoding Γ).enum acc = some (input.get ⟨k, hk⟩))
  (h_inputIndex : cfg.inputIndex = (k + 1) * (StandardEncoding Γ).W)
  (h_workIndex : cfg.workIndex = k)
  (h_work_lt : ∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
  (h_work_ge : ∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  (h_input : cfg.input = bitstreamFromInput input)
  (h_output : cfg.output = input.take k) :
  ∃ cfg',
    step (TM_generator (enc := StandardEncoding Γ) M) cfg = some cfg' ∧
    DecodeSymbolInv input cfg' (k := k + 1) (by omega) := by
  -- Unfold step and TM_generator
  simp only [step, TM_generator]
  rw [h_state, h_inputIndex, h_workIndex]
  -- We're in the case where bitsRead = W, so h_eq holds
  have h_eq : (StandardEncoding Γ).W = (StandardEncoding Γ).W := rfl
  have h_not_default : input.get ⟨k, hk⟩ ≠ default :=
    input_symbols_not_default input h_no_default hk
  simp only [↓reduceDIte, Int.reduceNeg]
  -- Now we construct the next configuration
  use {
    state := GenState.load {
      bitsRead := 0,
      acc := 0,
      accBound := by simp
    },
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := fun i => if i = cfg.workIndex then input.get ⟨k, hk⟩ else cfg.work i,
    workIndex := cfg.workIndex + 1,
    output := cfg.output ++ [input.get ⟨k, hk⟩]
  }
  constructor
  · simp only [List.get_eq_getElem, h_enum, List.get_eq_getElem, Int.reduceNeg,
      h_inputIndex, h_workIndex]
    have h_get_eq : input[k] = input.get ⟨k, hk⟩ := by rfl
    rw [h_get_eq]
    simp only [h_not_default, ↓reduceIte, add_zero]
  -- Prove DecodeSymbolInv
  unfold DecodeSymbolInv
  simp only [h_inputIndex, h_workIndex]
  constructor
  · trivial
  constructor
  · trivial
  constructor
  · rfl
  constructor
  · intro i hi
    by_cases h : i = k
    · -- case i = k
      subst h
      simp
    · -- case i ≠ k
      have hi' : i < k := by omega
      simp [h, h_work_lt i hi']
  constructor
  · intro i hi
    by_cases h : i = k
    · -- case i = k
      subst h
      -- show contradiction from the assumption
      have : ¬ (k + 1 ≤ (k : ℤ).toNat) := by
        simp
      cases hi with
      | inl hneg =>
          -- impossible: (k : ℤ) is not negative
          simp only at hneg
          exfalso
          have hnonneg : 0 ≤ (↑k : ℤ) := Int.natCast_nonneg k
          exact (lt_of_lt_of_le hneg hnonneg).false.elim
      | inr hge =>
          exact (this hge).elim
    · -- case i ≠ k
      simp only [h, ↓reduceIte]
      apply h_work_ge
      cases hi with
      | inl hneg =>
          exact Or.inl hneg
      | inr hge =>
          -- strengthen k+1 ≤ i.toNat to k ≤ i.toNat
          exact Or.inr (by omega)
  constructor
  · exact h_input
  · simp only [h_output]
    simp

lemma decodeOneSymbol {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ]
  [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  {k : ℕ} (hk : k < input.length)
:
  DecodeSymbolInv input cfg (k := k) (by omega) →
  ∃ cfg',
    StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfg' ∧
    DecodeSymbolInv input cfg' (k := k + 1) (by omega)
:= by
  intro h_sym
  let W := (StandardEncoding Γ).W
  have hWpos : W > 0 := (StandardEncoding Γ).W_pos
  -- Convert DecodeSymbolInv → DecodeBitInv at x = 0
  have h_bit0 :
    DecodeBitInv input cfg (k := k) (by omega)
      ⟨0, by
        have := hWpos
        omega⟩ :=
  by
    obtain ⟨h_state, h_inputIndex, h_workIndex,
            h_work_lt, h_work_ge, h_input, h_output⟩ := h_sym
    refine ⟨h_state, ?_, h_workIndex,
             h_work_lt, h_work_ge, h_input, h_output⟩
    simp [h_inputIndex]
  ----------------------------------------------------------------
  -- Step 1: decode W bits using induction on x : Fin W
  ----------------------------------------------------------------
  have decode_bits :
    ∃ cfgW,
      StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfgW ∧
      DecodeBitInv input cfgW (k := k) (by omega)
        ⟨W, by linarith⟩ :=
  by
    -- Induction on natural x < W
    have :
      ∀ x : ℕ, (hx : x ≤ W) →
        ∃ cfgx,
          StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfgx ∧
          DecodeBitInv input cfgx (k := k) (by omega)
            ⟨x, by linarith⟩ :=
    by
      intro x
      induction x with
      | zero =>
        intro _
        exact ⟨cfg, StepsTo.refl _, h_bit0⟩
      | succ x ih =>
        intro hx
        -- hx : x.succ ≤ W
        -- First get x ≤ W so we can apply the IH
        have hx_le : x ≤ W := by
          exact Nat.le_trans (Nat.le_succ x) hx
        obtain ⟨cfgx, h_steps, h_inv⟩ := ih hx_le
        -- Now show x < W so we can use decodeBitWithinSymbol
        have hx_lt : x < W := by
          exact Nat.lt_of_succ_le hx
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decodeBitWithinSymbol
            M input
            (by omega)
            ⟨x, hx_lt⟩
            cfgx
            h_inv
        refine ⟨cfg_next, ?_, h_next_inv⟩
        exact StepsTo.trans _
          h_steps
          ⟨1,
            Steps.step cfgx cfg_next cfg_next 0 h_step
              (Steps.refl _)⟩
    exact this W (Nat.le_refl _)
  obtain ⟨cfgW, h_steps_bits, h_invW⟩ := decode_bits
  ----------------------------------------------------------------
  -- Step 2: emit symbol using decodeSymbolWrite
  ----------------------------------------------------------------
  -- Extract the necessary components from DecodeBitInv at W
  obtain ⟨h_stateW, h_inputIndexW, h_workIndexW,
          h_work_ltW, h_work_geW, h_inputW, h_outputW⟩ := h_invW
  -- Use decoding correctness lemma
  have h_enum :
    (StandardEncoding Γ).enum
      (readBlockOfBitsW
        (bitstreamFromInput input)
        (WIDTH Γ * k)
        (WIDTH Γ)
        (WIDTH Γ)
        (by rfl))
      = some (input.get ⟨k, hk⟩) :=
    readBlockOfBits_decodes_to_input input hk
  have h_inputIndexW' :
    cfgW.inputIndex = (k + 1) * (StandardEncoding Γ).W :=
  by
    rw [h_inputIndexW]
    ring
  obtain ⟨cfg', h_step_write, h_final⟩ :=
    writeDecodedSymbol M input h_no_default hk
      cfgW
      _
      h_stateW
      h_enum
      h_inputIndexW'
      h_workIndexW
      h_work_ltW
      h_work_geW
      h_inputW
      h_outputW
  ----------------------------------------------------------------
  -- Combine everything
  ----------------------------------------------------------------
  refine ⟨cfg', ?_, h_final⟩
  exact StepsTo.trans _
    h_steps_bits
    ⟨1,
      Steps.step cfgW cfg' cfg' 0 h_step_write
        (Steps.refl _)⟩

lemma detectEOF {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (acc : Fin (2 ^ (StandardEncoding Γ).W))
  (h_state : cfg.state = GenState.load {
    bitsRead := ⟨(StandardEncoding Γ).W, by omega⟩,
    acc := acc,
    accBound := by simp; omega
  })
  (h_enum : (StandardEncoding Γ).enum acc = none)
  :
  ∃ cfg',
    step (TM_generator (enc := StandardEncoding Γ) M) cfg = some cfg' ∧
    cfg'.state = GenState.rewind ∧
    cfg'.inputIndex = cfg.inputIndex ∧
    cfg'.workIndex = cfg.workIndex - 1 ∧
    cfg'.work = cfg.work ∧
    cfg'.output = cfg.output
:= by
  -- Unfold step and TM_generator
  simp only [step, TM_generator]
  rw [h_state]
  -- We're in the GenState.load case with bitsRead = W
  have h_eq : (StandardEncoding Γ).W = (StandardEncoding Γ).W := rfl
  simp only [↓reduceDIte]
  -- The enum returns none, so we take the first branch
  rw [h_enum]
  simp only
  -- Construct the next configuration
  use {
    state := GenState.rewind,
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := cfg.work,
    workIndex := cfg.workIndex + (-1 : ℤ),
    output := cfg.output
  }
  constructor
  · -- Prove the step equation
    congr 1
    ext
    · rfl  -- state
    · rfl  -- input
    · simp  -- inputIndex (0 added)
    · -- work: show the conditional equals cfg.work
      simp only
      split_ifs with h
      · subst h
        rfl
      · rfl
    · rfl  -- workIndex
    · rfl  -- output
  constructor
  · -- cfg'.state = GenState.rewind
    rfl
  constructor
  · -- cfg'.inputIndex = cfg.inputIndex
    rfl
  constructor
  · -- cfg'.workIndex = cfg.workIndex - 1
    rfl
  constructor
  · -- cfg'.work = cfg.work
    rfl
  · -- cfg'.output = cfg.output
    rfl

lemma decodeEOFMarker {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_ready_for_last_symbol : DecodeSymbolInv input cfg (k := input.length) (by omega))
: ∃ cfg',
StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfg'
∧ (
  cfg'.state = GenState.rewind
∧ cfg'.workIndex = cfg.workIndex - 1
∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
∧ cfg'.output = input
) := by
  let W := (StandardEncoding Γ).W
  have hWpos : W > 0 := (StandardEncoding Γ).W_pos
  -- Convert DecodeSymbolInv → DecodeBitInv at x = 0
  have h_bit0 :
    DecodeBitInv input cfg (k := input.length) (by omega)
      ⟨0, by omega⟩ :=
  by
    obtain ⟨h_state, h_inputIndex, h_workIndex,
            h_work_lt, h_work_ge, h_input, h_output⟩ := h_ready_for_last_symbol
    refine ⟨h_state, ?_, h_workIndex,
             h_work_lt, h_work_ge, h_input, h_output⟩
    simp [h_inputIndex]
  ----------------------------------------------------------------
  -- Step 1: decode W bits using induction on x : Fin W
  ----------------------------------------------------------------
  have decode_bits :
    ∃ cfgW,
      StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfgW ∧
      DecodeBitInv input cfgW (k := input.length) (by omega)
        ⟨W, by linarith⟩ :=
  by
    -- Induction on natural x ≤ W
    have :
      ∀ x : ℕ, (hx : x ≤ W) →
        ∃ cfgx,
          StepsTo (TM_generator (enc := StandardEncoding Γ) M) cfg cfgx ∧
          DecodeBitInv input cfgx (k := input.length) (by omega)
            ⟨x, by linarith⟩ :=
    by
      intro x
      induction x with
      | zero =>
        intro _
        exact ⟨cfg, StepsTo.refl _, h_bit0⟩
      | succ x ih =>
        intro hx
        -- hx : x.succ ≤ W
        have hx_le : x ≤ W := Nat.le_trans (Nat.le_succ x) hx
        obtain ⟨cfgx, h_steps, h_inv⟩ := ih hx_le
        -- Now show x < W so we can use decodeBitWithinSymbol
        have hx_lt : x < W := Nat.lt_of_succ_le hx
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decodeBitWithinSymbol
            M input
            (by omega)
            ⟨x, hx_lt⟩
            cfgx
            h_inv
        refine ⟨cfg_next, ?_, h_next_inv⟩
        exact StepsTo.trans _
          h_steps
          ⟨1,
            Steps.step cfgx cfg_next cfg_next 0 h_step
              (Steps.refl _)⟩
    exact this W (Nat.le_refl _)
  obtain ⟨cfgW, h_steps_bits, h_invW⟩ := decode_bits
  ----------------------------------------------------------------
  -- Step 2: detect EOF using detectEOF
  ----------------------------------------------------------------
  -- Extract components from DecodeBitInv at W
  obtain ⟨h_stateW, h_inputIndexW, h_workIndexW,
          h_work_ltW, h_work_geW, h_inputW, h_outputW⟩ := h_invW
  -- Get the accumulated value
  let acc := readBlockOfBitsW (bitstreamFromInput input) (WIDTH Γ * input.length) W W (by omega)
  -- Prove that enum returns none for the EOF marker
  have h_enum : (StandardEncoding Γ).enum acc = none := EOF_enum_is_none input
  obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩ :=
    h_ready_for_last_symbol
  -- cfgW.inputIndex = input.length * W + W = (input.length + 1) * W
  have h_inputIndexW' : cfgW.inputIndex = (input.length + 1) * (StandardEncoding Γ).W := by
    rw [h_inputIndexW]
    ring
  -- cfgW.output = input.take input.length = input
  have h_outputW' : cfgW.output = input := by
    rw [h_outputW]
    simp [List.take_length]
  obtain ⟨cfg', h_step_eof, h_state', h_inputIndex', h_workIndex', h_work', h_output'⟩ :=
    detectEOF M cfgW acc
      h_stateW
      h_enum
  ----------------------------------------------------------------
  -- Combine everything
  ----------------------------------------------------------------
  refine ⟨cfg', ?_, h_state', ?_, ?_, ?_, ?_, ?_⟩
  · -- Prove StepsTo
    exact StepsTo.trans _
      h_steps_bits
      ⟨1, Steps.step cfgW cfg' cfg' 0 h_step_eof (Steps.refl _)⟩
  · -- Prove workIndex: cfg'.workIndex = cfg.workIndex - 1
    rw [h_workIndex', h_workIndexW, h_workIndex]
  · -- Prove work for i < input.length
    intro i hi
    rw [h_work']
    exact h_work_ltW i hi
  · -- Prove work for i ≥ input.length
    intro i hi
    rw [h_work']
    apply h_work_geW
    exact Or.inr hi
  · -- Prove work for i < 0
    intro i hi
    rw [h_work']
    apply h_work_geW
    exact Or.inl hi
  · -- Prove output: cfg'.output = input
    rw [h_output', h_outputW']

lemma weGetReadyToRewind {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
: ∃ cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)),
    let gen := TM_generator (enc := StandardEncoding Γ) M
    cfg.state = GenState.rewind
    ∧ cfg.workIndex = input.length - 1
    ∧ (∀ i (h : i < input.length),
        cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length →
        cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 →
        cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg := by
  set gen := TM_generator (enc := StandardEncoding Γ) M
  let initialCfg := (initConfig gen
    (bitstreamFromInput input))
  have h_base_inv : DecodeSymbolInv input initialCfg (k := 0) (by omega) := by
    unfold DecodeSymbolInv
    simp only [initConfig, bitstreamFromInput, List.get_eq_getElem, Bool.if_false_right, zero_mul,
      CharP.cast_eq_zero, not_lt_zero, Int.toNat_natCast, IsEmpty.forall_iff, implies_true,
      zero_le, or_true, forall_const, List.take_zero, and_self, and_true, true_and, initialCfg]
    unfold gen
    simp [TM_generator]
  have h_read_k_inputs :
    ∀ i (hi : i ≤ input.length),
      ∃ cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)),
        DecodeSymbolInv input cfg' hi
        ∧ StepsTo gen initialCfg cfg'
        := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨initialCfg, h_base_inv, by exact StepsTo.refl gen (cfg := initialCfg)⟩
    | succ i ih =>
      intro h_le
      have h_lt : i < input.length :=
        Nat.lt_of_succ_le h_le
      have h_prev :=
        ih (Nat.le_of_lt h_lt)
      rcases h_prev with ⟨cfg_i, hInv_i, h_steps_to_i⟩
      have h_next :=
        decodeOneSymbol M input h_no_default cfg_i h_lt hInv_i
      obtain ⟨cfg', h_steps_cfg_i_to_cfg', h_inv_cfg'⟩ := h_next
      have h_steps_to_init_cfg' :
          StepsTo gen initialCfg cfg' := by
            exact StepsTo.trans gen (cfg1 := initialCfg) (cfg2 := cfg_i) (cfg3 := cfg')
              h_steps_to_i h_steps_cfg_i_to_cfg'
      use cfg'
  have h_all_inputs_decoded :=
    h_read_k_inputs input.length (le_rfl)
  obtain ⟨cfg_all_decoded, h_inv_all_decoded, h_initial_steps_to_cfg_all_decoded⟩ :=
    h_all_inputs_decoded
  obtain ⟨cfg_final, h_properties_of_cfg_final⟩ := decodeEOFMarker M input cfg_all_decoded
    h_inv_all_decoded
  rcases h_properties_of_cfg_final with
    ⟨h_steps_cfg_final, h_state_cfg_final, h_workIndex_cfg_final, h_work_lt_cfg_final,
     h_work_ge_cfg_final, h_work_neg_cfg_final, h_output_cfg_final⟩
  use cfg_final
  have h_initial_stepsto_final :
    StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg_final :=
      StepsTo.trans gen h_initial_steps_to_cfg_all_decoded h_steps_cfg_final
  have h_cfg_final_work_index_eq_input_length_minus_one :
    cfg_final.workIndex = input.length - 1 := by
    have h_work_index_all_decoded := by
      rcases h_inv_all_decoded with ⟨_, _, workIndex_eq_k, _, _, _⟩
      exact workIndex_eq_k
    rw [h_workIndex_cfg_final]
    omega
  refine ⟨h_state_cfg_final,
        h_cfg_final_work_index_eq_input_length_minus_one,
        h_work_lt_cfg_final,
        h_work_ge_cfg_final,
        h_work_neg_cfg_final,
        h_output_cfg_final,
        h_initial_stepsto_final⟩

lemma rewindWithNonNegativeIndexOneStep {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ default ∉ input)
: step (TM_generator (enc := StandardEncoding Γ) M) cfg = some {
    state := GenState.rewind,
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := cfg.work,
    workIndex := cfg.workIndex - 1,
    output := cfg.output
} := by
  obtain ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩ := h
  unfold step TM_generator
  simp only [h_state]
  -- Show that cfg.work (cfg.workIndex) ≠ default
  have h_not_blank : cfg.work cfg.workIndex ≠ default := by
    have h_eq : cfg.work cfg.workIndex = input.get ⟨cfg.workIndex.toNat, by omega⟩ := by
      have := h_work_input cfg.workIndex.toNat (by omega)
      convert this using 2
      simp only [Int.ofNat_toNat, left_eq_sup]
      exact h_idx_nonneg
    rw [h_eq]
    intro h_contra
    apply h_no_blank
    rw [← h_contra]
    exact List.get_mem input ⟨cfg.workIndex.toNat, by omega⟩
  simp only [if_neg h_not_blank]
  norm_num
  constructor
  · -- Prove function equality
    funext x
    split_ifs with hx
    · rw [hx]
    · rfl
  · -- Prove cfg.workIndex + -1 = cfg.workIndex - 1
    ring

lemma rewindWithNonNegativeIndexManySteps {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := TM_generator (enc := StandardEncoding Γ) M
    cfg'.state = GenState.rewind
    ∧ cfg'.workIndex = -1
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := TM_generator (enc := StandardEncoding Γ) M
  obtain ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_work_ge,
          h_work_neg, h_output, h_no_blank⟩ := h
  -- Induction on cfg.workIndex.toNat
  match n : cfg.workIndex.toNat with
  | 0 =>
    -- Base case: cfg.workIndex = 0
    have h_idx_eq : cfg.workIndex = 0 := by omega
    -- Take one step to get to workIndex = -1
    let cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)) := {
      state := GenState.rewind,
      input := cfg.input,
      inputIndex := cfg.inputIndex,
      work := cfg.work,
      workIndex := cfg.workIndex - 1,
      output := cfg.output
    }
    use cfg'
    constructor
    · rfl
    constructor
    · simp [cfg', h_idx_eq]
    constructor
    · exact h_work_input
    constructor
    · exact h_work_ge
    constructor
    · exact h_work_neg
    constructor
    · exact h_output
    · use 1
      apply Steps.step cfg cfg' cfg' 0
      · exact rewindWithNonNegativeIndexOneStep M input cfg
          ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩
      · exact Steps.refl cfg'
  | m + 1 =>
    -- Inductive case
    have h_idx_eq : cfg.workIndex = m + 1 := by omega
    -- Take one step
    let cfg_next : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)) := {
      state := GenState.rewind,
      input := cfg.input,
      inputIndex := cfg.inputIndex,
      work := cfg.work,
      workIndex := cfg.workIndex - 1,
      output := cfg.output
    }
    have h_step : step gen cfg = some cfg_next :=
      rewindWithNonNegativeIndexOneStep M input cfg
        ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩
    --Apply IH to cfg_next
    have h_ih_input : cfg_next.state = GenState.rewind
       ∧ cfg_next.workIndex < input.length
       ∧ cfg_next.workIndex ≥ 0
       ∧ (∀ i (h : i < input.length), cfg_next.work (i : ℤ) = input.get ⟨i, h⟩)
       ∧ (∀ i : ℕ, i ≥ input.length → cfg_next.work (i : ℤ) = (default : Γ))
       ∧ (∀ i : ℤ, i < 0 → cfg_next.work (i : ℤ) = (default : Γ))
       ∧ cfg_next.output = input
       ∧ default ∉ input := by
         simp only [Order.sub_one_lt_iff, Int.sub_nonneg,
           List.get_eq_getElem, ge_iff_le, true_and, cfg_next]
         refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨cfg', h_final⟩ := rewindWithNonNegativeIndexManySteps M input cfg_next h_ih_input
    use cfg'
    refine ⟨h_final.1, h_final.2.1, h_final.2.2.1, h_final.2.2.2.1,
      h_final.2.2.2.2.1, h_final.2.2.2.2.2.1, ?_⟩
    obtain ⟨k, h_steps⟩ := h_final.2.2.2.2.2.2
    use k + 1
    exact Steps.step cfg cfg_next cfg' k h_step h_steps
termination_by cfg.workIndex.toNat

lemma rewindWithNegativeIndex {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = -1
    ∧ cfg.work (-1) = (default : Γ))
: step (TM_generator (enc := StandardEncoding Γ) M) cfg = some {
    state := GenState.sim (default : Λ),
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := cfg.work,
    workIndex := 0,
    output := cfg.output
} := by
  obtain ⟨h_state, h_idx, h_blank⟩ := h
  unfold step TM_generator
  simp only [h_state, h_idx, h_blank, if_true]
  norm_num
  funext x
  split_ifs with hx
  · rw [hx, h_blank]
  · rfl

lemma rewindingLeadsToSimulationReadiness {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = input.length - 1
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := TM_generator (enc := StandardEncoding Γ) M
    cfg'.state = GenState.sim (default : Λ)
    ∧ cfg'.workIndex = 0
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := TM_generator (enc := StandardEncoding Γ) M
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low, h_output, h_no_default⟩
    := h
  -- Bind the length to avoid generalization issues
  by_cases h_empty : input.length = 0
  · -- Empty input case
    have h_idx_neg : cfg.workIndex = -1 := by simp [h_idx, h_empty]
    have h_work_neg : cfg.work (-1) = default := by
      apply h_work_blank_low
      norm_num
    have h_step := rewindWithNegativeIndex M cfg ⟨h_state, h_idx_neg, h_work_neg⟩
    use {
      state := GenState.sim (default : Λ),
      input := cfg.input,
      inputIndex := cfg.inputIndex,
      work := cfg.work,
      workIndex := 0,
      output := cfg.output
    }
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simp [h_empty] at hi
    · intro i hi
      exact h_work_blank_high i hi
    · intro i hi
      exact h_work_blank_low i hi
    · exact h_output
    · use 1
      apply Steps.step cfg _ _ 0 h_step
      exact Steps.refl _
  · -- Non-empty input case
    have h_length_pos : input.length > 0 := by omega
    have h_idx_nonneg : cfg.workIndex ≥ 0 := by
      rw [h_idx]
      omega
    have h_idx_bound : cfg.workIndex < input.length := by
      rw [h_idx]
      omega
    have h_many_conditions : cfg.state = GenState.rewind
      ∧ cfg.workIndex < input.length
      ∧ cfg.workIndex ≥ 0
      ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
      ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = default)
      ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = default)
      ∧ cfg.output = input
      ∧ default ∉ input :=
        ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input,
         h_work_blank_high, h_work_blank_low, h_output, h_no_default⟩
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output,
            h_steps_to_rewind⟩ :=
      rewindWithNonNegativeIndexManySteps M input cfg h_many_conditions
    have h_rewind_work_neg : rewindCfg.work (-1) = default :=
      h_rewind_work_blank_low (-1) (by omega)
    have h_step := rewindWithNegativeIndex M rewindCfg
      ⟨h_rewind_state, h_rewind_idx, h_rewind_work_neg⟩
    let finalCfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)) := {
      state := GenState.sim (default : Λ),
      input := rewindCfg.input,
      inputIndex := rewindCfg.inputIndex,
      work := rewindCfg.work,
      workIndex := 0,
      output := rewindCfg.output
    }
    use finalCfg
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      exact h_rewind_work_input i hi
    · intro i hi
      exact h_rewind_work_blank_high i hi
    · intro i hi
      exact h_rewind_work_blank_low i hi
    · exact h_rewind_output
    · obtain ⟨n1, steps1⟩ := h_steps_to_rewind
      use n1 + 1
      have step_final : Steps gen rewindCfg finalCfg 1 := by
        apply Steps.step rewindCfg finalCfg finalCfg 0 h_step
        exact Steps.refl _
      exact Steps.trans steps1 step_final

lemma weGetReadyToSimulate {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
: ∃ cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)),
    let gen := TM_generator (enc := StandardEncoding Γ) M
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < input.length),
        cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length →
        cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 →
        cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg := by
    let gen := TM_generator (enc := StandardEncoding Γ) M
    -- First, get to the rewind state
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_init_to_rewind⟩ :=
      weGetReadyToRewind M input h_no_default
    -- Build the hypothesis for rewindingLeadsToSimulationReadiness
    have h_rewind_conditions : rewindCfg.state = GenState.rewind
      ∧ rewindCfg.workIndex = input.length - 1
      ∧ (∀ i (h : i < input.length), rewindCfg.work (i : ℤ) = input.get ⟨i, h⟩)
      ∧ (∀ i : ℕ, i ≥ input.length → rewindCfg.work (i : ℤ) = (default : Γ))
      ∧ (∀ i : ℤ, i < 0 → rewindCfg.work (i : ℤ) = (default : Γ))
      ∧ rewindCfg.output = input
      ∧ default ∉ input
       := by
        exact ⟨h_rewind_state, h_rewind_idx, h_rewind_work_input,
               h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_no_default⟩
    -- Apply rewindingLeadsToSimulationReadiness with rewindCfg
    obtain ⟨simCfg, h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
            h_sim_work_blank_low, h_sim_output, h_rewind_to_sim⟩ :=
      rewindingLeadsToSimulationReadiness M input rewindCfg h_rewind_conditions
    -- Return simCfg with all required properties
    use simCfg
    refine ⟨h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
            h_sim_work_blank_low, h_sim_output, ?_⟩
    -- Show StepsTo from init to sim via rewind
    obtain ⟨n1, steps1⟩ := h_init_to_rewind
    obtain ⟨n2, steps2⟩ := h_rewind_to_sim
    use n1 + n2
    exact Steps.trans steps1 steps2

structure configurationsMatch {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (genCfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ Λ) : Prop where
  states_match : genCfg.state = GenState.sim (Λ := Λ) (Γ := Γ) (enc := StandardEncoding Γ) tm0Cfg.q
  heads_match : genCfg.work genCfg.workIndex = tm0Cfg.Tape.head
  tape_match_right : ∀ (d : ℕ), genCfg.work (genCfg.workIndex + 1 + d) =
    Turing.ListBlank.nth tm0Cfg.Tape.right d
  tape_match_left : ∀ (d : ℕ), genCfg.work (genCfg.workIndex - 1 - d) =
    Turing.ListBlank.nth tm0Cfg.Tape.left d

def maybeConfigurationsMatch {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (maybeGenCfg : Option (GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ))))
  (maybeTm0Cfg : Option (Turing.TM0.Cfg Γ Λ)) : Prop :=
match maybeGenCfg, maybeTm0Cfg with
| none, none => True
| some genCfg, some tm0Cfg => configurationsMatch genCfg tm0Cfg
| _, _ => False

lemma matchingConfigurationsStepSimultaneously {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine Γ Λ)
  (genCfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ Λ)
  (h_match : configurationsMatch genCfg tm0Cfg)
  : maybeConfigurationsMatch (step (TM_generator M) genCfg) (Turing.TM0.step M tm0Cfg) := by
  have h_list_blank : ∀ (lb : Turing.ListBlank Γ)
      (x : ℕ), 1 ≤ x → lb.tail.nth x = lb.tail.tail.nth (x - 1) := by
    intros lb x hx
    -- Use nth_succ on lb.tail
    rw [← Turing.ListBlank.nth_succ lb.tail (x - 1)]
      -- Simplify the RHS: (x - 1) + 1 = x
    rw [Nat.sub_add_cancel hx]
  -- Extract the matching conditions
  have h_state := h_match.states_match
  have h_head := h_match.heads_match
  have h_right := h_match.tape_match_right
  have h_left := h_match.tape_match_left
  -- Unfold the step functions
  unfold step TM_generator Turing.TM0.step maybeConfigurationsMatch
  -- The generator is in sim state, so we know genCfg.state = GenState.sim tm0Cfg.q
  simp only [h_state]
  -- Case split on what M does at the current state and tape head
  cases h_M : M tm0Cfg.q tm0Cfg.Tape.head with
  | none =>
      rw [h_head]
      rw [h_M]
      simp
  | some val =>
    -- Both machines continue
    obtain ⟨q', stmt⟩ := val
    simp only [Int.reduceNeg, Option.map_some, reduceCtorEq, imp_self, implies_true]
    -- Case split on the statement type
    cases stmt with
    | write a =>
        simp only [h_M, h_head]
        constructor
        · -- states_match
          rfl
        · -- heads match
          simp
          rfl
        · -- tape_match_right
          intro d
          simp only [add_zero]
          have h_ne : genCfg.workIndex + 1 + ↑d ≠ genCfg.workIndex := by
            intro eq
            linarith [Int.ofNat_le_ofNat_of_le (Nat.zero_le d)]
          simp only [if_neg h_ne]
          exact h_match.tape_match_right d
        · -- tape_match_left
          intro d
          simp only [add_zero]
          have h_ne : genCfg.workIndex - 1 - ↑d ≠ genCfg.workIndex := by
            intro eq
            linarith [Int.ofNat_le_ofNat_of_le (Nat.zero_le d)]
          simp only [if_neg h_ne]
          exact h_match.tape_match_left d
    | move dir =>
      -- Move operation
      simp only [Int.reduceNeg, reduceCtorEq, imp_self, implies_true]
      cases dir with
      | left =>
        -- Move left
        -- Compute next generator config
        have h_next_gen : step (TM_generator M) genCfg = some {
          state := GenState.sim q'
          input := genCfg.input
          inputIndex := genCfg.inputIndex
          work := genCfg.work
          workIndex := genCfg.workIndex - 1
          output := genCfg.output
        } := by
          unfold step TM_generator
          simp only [h_state]
          simp only [h_head]
          simp only [h_M, add_zero, Int.reduceNeg, Option.some.injEq,
            GeneratorConfig.mk.injEq, and_true, true_and]
          constructor
          · funext x
            by_cases hx : x = genCfg.workIndex
            · simp [hx, h_head]
            · simp [hx]
          · linarith
        -- Compute next TM0 config
        have h_next_tm : Turing.TM0.step M tm0Cfg = some {
          q := q'
          Tape := tm0Cfg.Tape.move Turing.Dir.left
        } := by
          simp only [Turing.TM0.step, h_M]
          rfl
        simp only [h_head, h_M, add_zero, Int.reduceNeg]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rfl
        · simp [Turing.Tape.move]
          simpa using h_left 0
        · intro d
          simp only [Turing.Tape.move]
          split
          · have h_d_eq_0 : d = 0 := by omega
            simp [h_d_eq_0]
          · have h_d_neq_0 : d ≠ 0 := by omega
            have h_helper : genCfg.workIndex + -1 + 1 + ↑d = genCfg.workIndex + 1 + ↑(d - 1) :=
              by omega
            rw [h_helper, h_right (d - 1)]
            have h_d_gt_0 : d > 0 := by omega
            rw [← Nat.succ_pred_eq_of_pos h_d_gt_0, Turing.ListBlank.nth_succ,
              Turing.ListBlank.tail_cons]
            have : d.pred.succ = d := by
              simp [Nat.pred_eq_sub_one]
              omega
            rw [this, Nat.pred_eq_sub_one]
        · intro d
          simp only [Turing.Tape.move]
          have impossible : ¬ (genCfg.workIndex + - 1 - 1 - ↑d = genCfg.workIndex) := by omega
          simp only [Int.reduceNeg, if_neg impossible]
          have h_helper : genCfg.workIndex + -1 - 1 - ↑d = genCfg.workIndex - 1 - ↑(d + 1) :=
            by omega
          rw [h_helper, h_left (d + 1)]
          simp only [Turing.ListBlank.nth_succ]
      | right =>
        -- Move right
        -- Compute next generator config
        have h_next_gen : step (TM_generator M) genCfg = some {
          state := GenState.sim q'
          input := genCfg.input
          inputIndex := genCfg.inputIndex
          work := genCfg.work
          workIndex := genCfg.workIndex + 1
          output := genCfg.output
        } := by
          unfold step TM_generator
          simp only [h_state]
          simp only [h_head]
          simp only [h_M, add_zero, Option.some.injEq,
            GeneratorConfig.mk.injEq, and_true, true_and]
          funext x
          split_ifs with hx
          · rw[hx]
            exact symm h_head
          · rfl
        -- Compute next TM0 config
        have h_next_tm : Turing.TM0.step M tm0Cfg = some {
          q := q'
          Tape := tm0Cfg.Tape.move Turing.Dir.right
        } := by
          simp only [Turing.TM0.step, h_M]
          rfl
        simp only [h_head, h_M, add_zero]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rfl
        · simp [Turing.Tape.move]
          simpa using h_right 0
        · intro d
          simp only [Turing.Tape.move]
          have impossible : ¬ (genCfg.workIndex + 1 + 1 + ↑d = genCfg.workIndex) := by omega
          simp only [if_neg impossible]
          have h_helper : genCfg.workIndex + 1 + 1 + ↑d = genCfg.workIndex + 1 + ↑(d + 1) :=
            by omega
          rw [h_helper, h_right (d + 1)]
          simp only [Turing.ListBlank.nth_succ]
        · intro d
          simp only [Turing.Tape.move]
          split
          · have h_d_eq_0 : d = 0 := by omega
            simp [h_d_eq_0]
          · have h_d_neq_0 : d ≠ 0 := by omega
            have h_helper : genCfg.workIndex + 1 - 1 - ↑d = genCfg.workIndex - 1 - ↑(d - 1) :=
              by omega
            rw [h_helper, h_left (d - 1)]
            have h_d_gt_0 : d > 0 := by omega
            rw [← Nat.succ_pred_eq_of_pos h_d_gt_0, Turing.ListBlank.nth_succ,
              Turing.ListBlank.tail_cons]
            have : d.pred.succ = d := by
              simp [Nat.pred_eq_sub_one]
              omega
            rw [this, Nat.pred_eq_sub_one]

lemma simStaysInSimAndPreservesOutput {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (cfg cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_state : ∃ q, cfg.state = GenState.sim q)
  (h_step : step (TM_generator M) cfg = some cfg') :
  cfg'.output = cfg.output ∧ (∃ q', cfg'.state = GenState.sim q') := by
  obtain ⟨q, hq⟩ := h_state
  unfold step TM_generator at h_step
  simp only [hq] at h_step
  cases h_M : M q (cfg.work cfg.workIndex) with
  | none => simp [h_M] at h_step
  | some val =>
    obtain ⟨q', stmt⟩ := val
    simp only [h_M] at h_step
    cases stmt with
    | write g =>
      simp only [Option.some.injEq] at h_step
      constructor
      · rw [← h_step]
      · rw [← h_step]; exact ⟨q', rfl⟩
    | move dir =>
      cases dir with
      | left =>
        simp only [Option.some.injEq] at h_step
        constructor
        · rw [← h_step]
        · rw [← h_step]; exact ⟨q', rfl⟩
      | right =>
        simp only [Option.some.injEq] at h_step
        constructor
        · rw [← h_step]
        · rw [← h_step]; exact ⟨q', rfl⟩

lemma simulationWorksOnceWeAreReady {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_cfg :
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ default ∉ input
  ) :
  ∃ haltCfg,
    let gen := TM_generator (enc := StandardEncoding Γ) M
    StepsTo gen cfg haltCfg
    ∧ haltingConfig gen haltCfg
    ∧ haltCfg.output = input := by
  --
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low,
    h_output, h_no_default⟩ := h_cfg
  --
  -- Step 1: Show `cfg` matches the TM0 initial configuration
  have h_match_init : configurationsMatch cfg (Turing.TM0.init input) := by
    constructor
    · -- states_match
      exact h_state
    · -- heads_match
      rw [h_idx]
      unfold Turing.TM0.init Turing.Tape.mk₁
      cases h : input with
      | nil =>
        simp only [Turing.Tape.mk₂, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_nil]
        have : input.length = 0 := by simp [h]
        exact h_work_blank_high 0 (by omega)
      | cons head tail =>
        simp only [Turing.Tape.mk₂, Turing.Tape.mk'_head, Turing.ListBlank.head_mk, List.headI_cons]
        convert h_work_input 0 (by simp [h])
        simp [h]
    · -- right_match
      intro d
      unfold Turing.TM0.init Turing.Tape.mk₁
      rw [h_idx]
      simp only [Turing.ListBlank.nth]
      cases h : input with
      | nil =>
        simp only [zero_add, Turing.Tape.mk₂, Turing.Tape.mk'_right,
          Turing.ListBlank.tail_mk, List.tail_nil]
        have : input.length = 0 := by simp [h]
        exact h_work_blank_high (1 + d) (by simp [h])
      | cons head tail =>
        simp only [zero_add, Turing.Tape.mk₂, Turing.ListBlank.mk,
            Turing.Tape.mk'_right, Turing.ListBlank.tail,
            Quotient.mk'']
        simp only [List.getI, List.getD_eq_getElem?_getD]
        by_cases hd : d < tail.length
        · -- d is within tail bounds
          have hget : tail[d]? = some (tail[d]) := by
            exact List.getElem?_eq_getElem hd
          simp only [Quotient.liftOn'_mk'', List.tail_cons, hget, Option.getD_some]
          have : tail[d] = input.get ⟨d + 1, by simp [h]; omega⟩ := by
            simp [h]
          rw [this]
          convert h_work_input (1 + d) (by simp [h]; omega) using 2
          ring_nf
        · -- d ≥ tail.length, so getElem? returns none
          simp only [Quotient.liftOn'_mk'', List.tail_cons]
          have : tail[d]? = none := by
            rw [List.getElem?_eq_none]
            omega
          simp only [this, Option.getD_none]
          exact h_work_blank_high (1 + d) (by simp [h]; omega)
    · -- left_match
      intro d
      unfold Turing.TM0.init Turing.Tape.mk₁
      rw [h_idx]
      simp only [zero_sub, Int.reduceNeg, Turing.ListBlank.nth, Turing.Tape.mk₂,
        Turing.Tape.mk'_left]
      have : (0 : ℤ) - 1 - (d : ℤ) < 0 := by omega
      exact h_work_blank_low _ this
  --
  -- Step 2: Use halting assumption to get a halting TM0 configuration
  obtain ⟨tmCfg, h_reaches, h_tm_halt⟩ : ∃ tmCfg,
      Turing.TM0.Reaches M (Turing.TM0.init input) tmCfg ∧ Turing.TM0.step M tmCfg = none := by
    unfold Turing.TM0.eval at h_halts
    obtain ⟨output, h_out⟩ := Part.dom_iff_mem.mp h_halts
    rw [Part.mem_map_iff] at h_out
    obtain ⟨cfg, h_cfg, _⟩ := h_out
    rw [Turing.mem_eval] at h_cfg
    obtain ⟨h_reaches, h_halt⟩ := h_cfg
    exact ⟨cfg, h_reaches, h_halt⟩
  --
  -- Step 3: Induction over `Reaches` to propagate `configurationsMatch` through steps
  have h_sim :
    ∀ {tmCfg cfg},
      Turing.TM0.Reaches M (Turing.TM0.init input) tmCfg →
      configurationsMatch cfg (Turing.TM0.init input) →
      (∃ q, cfg.state = GenState.sim q) →
      cfg.output = input →
      ∃ genCfg,
        let gen := TM_generator (enc := StandardEncoding Γ) M
        StepsTo gen cfg genCfg ∧ configurationsMatch genCfg tmCfg
          ∧ (∃ q, genCfg.state = GenState.sim q) ∧ genCfg.output = input := by
    intro tmCfg cfg h_reaches h_match h_sim_state h_out
    induction h_reaches with
    | refl =>
      exact ⟨cfg, ⟨0, Steps.refl cfg⟩, h_match, h_sim_state, h_out⟩
    | @tail b c prev one_step IH =>
      obtain ⟨genCfg₁, h_ih_properties⟩ := IH
      dsimp at h_ih_properties
      obtain ⟨h_steps₁, h_match₁, h_sim_state₁, h_out₁⟩ := h_ih_properties
      have h_sim_step := matchingConfigurationsStepSimultaneously M genCfg₁ b h_match₁
      unfold maybeConfigurationsMatch at h_sim_step
      rw [one_step] at h_sim_step
      cases h_gen_step : step (TM_generator M) genCfg₁ with
      | none =>
        rw [h_gen_step] at h_sim_step
        contradiction
      | some genCfg₂ =>
        rw [h_gen_step] at h_sim_step
        use genCfg₂
        constructor
        · obtain ⟨n, h_n⟩ := h_steps₁
          use n + 1
          have one_step_gen : Steps (TM_generator M) genCfg₁ genCfg₂ 1 :=
            Steps.step genCfg₁ genCfg₂ genCfg₂ 0 h_gen_step (Steps.refl genCfg₂)
          exact Steps.trans h_n one_step_gen
        constructor
        · exact h_sim_step
        · -- Use simStaysInSimAndPreservesOutput
          have ⟨h_preserve_out, h_stay_sim⟩ :=
            simStaysInSimAndPreservesOutput M genCfg₁ genCfg₂ h_sim_state₁ h_gen_step
          rw [h_preserve_out, h_out₁]
          simp only [and_true]
          exact h_stay_sim
  --
  -- Step 4: Apply the simulation lemma to reach the halting configuration
  obtain ⟨haltCfg, h_steps, h_match, _, h_output_input⟩ :=
    h_sim h_reaches h_match_init (by use (default : Λ)) h_output
  --
  -- Step 5: Return the final configuration
  use haltCfg
  have h_haltCfg_halts : haltingConfig
      (TM_generator (enc := StandardEncoding Γ) M) haltCfg := by
    unfold haltingConfig
    have h_sim_halt := matchingConfigurationsStepSimultaneously M haltCfg tmCfg h_match
    unfold maybeConfigurationsMatch at h_sim_halt
    rw [h_tm_halt] at h_sim_halt
    cases h_gen : step (TM_generator M) haltCfg with
    | none => rfl
    | some _ =>
      rw [h_gen] at h_sim_halt
      contradiction
  --
  refine ⟨h_steps, h_haltCfg_halts, h_output_input⟩

theorem anything_a_TM0_recognises_can_be_generated_by_its_TM_generator {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  (h_halts : (Turing.TM0.eval M input).Dom) :
  input ∈ (generated_language (TM_generator (enc := StandardEncoding Γ) M)).val := by
    let enc := StandardEncoding Γ
    let gen := (TM_generator (enc := enc) M)
    rcases weGetReadyToSimulate M input h_no_default
      with ⟨
        readyCfg,
        h_readyCfg_initial_state,
        h_readyCfg_work_index_zero,
        h_readyCfg_work_tape_contains_input,
        h_readyCfg_work_tape_blank_above,
        h_readyCfg_work_tape_blank_below,
        h_readyCfg_output_is_input,
        h_initial_stepsTo_readyCfg
      ⟩
    -- Build the hypothesis needed for simulationWorksOnceWeAreReady
    have h_ready : readyCfg.state = GenState.sim (default : Λ)
      ∧ readyCfg.workIndex = 0
      ∧ (∀ i (h : i < input.length), readyCfg.work (i : ℤ) = input.get ⟨i, h⟩)
      ∧ (∀ i : ℕ, i ≥ input.length → readyCfg.work (i : ℤ) = (default : Γ))
      ∧ (∀ i : ℤ, i < 0 → readyCfg.work i = (default : Γ))
      ∧ readyCfg.output = input
      ∧ default ∉ input := by
        exact ⟨h_readyCfg_initial_state, h_readyCfg_work_index_zero,
              h_readyCfg_work_tape_contains_input, h_readyCfg_work_tape_blank_above,
              h_readyCfg_work_tape_blank_below, h_readyCfg_output_is_input, h_no_default⟩
    rcases simulationWorksOnceWeAreReady M input h_halts readyCfg h_ready
      with ⟨haltCfg, h_steps_to_halt, h_is_halting, h_halt_output⟩
    --
    have h_whole_run : StepsTo gen (initConfig gen (bitstreamFromInput input)) haltCfg := by
      obtain ⟨n1, h1⟩ := h_initial_stepsTo_readyCfg
      obtain ⟨n2, h2⟩ := h_steps_to_halt
      use n1 + n2
      exact Steps.trans h1 h2
    --
    have h_computes : Computes gen (initConfig gen (bitstreamFromInput input)) haltCfg.output :=
      StepsTo.computes h_whole_run h_is_halting
    rw [h_halt_output] at h_computes
    --
    -- Show input ∈ generatedLanguage gen
    use bitstreamFromInput input

theorem anything_a_TM_generator_generates_is_recognised_by_its_TM0 {Γ Λ : Type u}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  (h_generated : input ∈ (generated_language (TM_generator (enc := StandardEncoding Γ) M)).val) :
  input ∈ (TM0_language M (Γ := Γ) (Λ := Λ)).val := by
  let enc := StandardEncoding Γ
  let gen := (TM_generator (enc := enc) M)
  sorry

end GenerationByTM0Simulation

lemma language_TM0_subset_language_TM_generator {Γ Λ : Type u}
  [Fintype Λ] [Inhabited Λ]
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) :
  (TM0_language M (Γ := Γ) (Λ := Λ)).val
  ⊆
  (generated_language (GenerationByTM0Simulation.TM_generator M
    (Λ := Λ)
    (Γ := Γ)
    (enc := (StandardEncoding Γ)))).val := by
  intro input h_in_TM0_lang
  obtain ⟨h_no_default, h_halts⟩ := h_in_TM0_lang
  exact GenerationByTM0Simulation.anything_a_TM0_recognises_can_be_generated_by_its_TM_generator
    M input h_no_default h_halts

lemma language_TM_generator_subset_language_TM0 {Γ Λ : Type u}
  [Fintype Λ] [Inhabited Λ]
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) :
  (generated_language (GenerationByTM0Simulation.TM_generator M
    (Λ := Λ)
    (Γ := Γ)
    (enc := (StandardEncoding Γ)))).val
  ⊆
  (TM0_language M (Γ := Γ) (Λ := Λ)).val
 := by
  intro input h_generated
  have h_no_default : default ∉ input :=
    (generated_language (GenerationByTM0Simulation.TM_generator M
      (Λ := Λ)
      (Γ := Γ)
      (enc := (StandardEncoding Γ)))).property input h_generated
  exact GenerationByTM0Simulation.anything_a_TM_generator_generates_is_recognised_by_its_TM0
    M input h_no_default h_generated

lemma language_TM0_eq_language_TM_generator {Γ Λ : Type u}
  [Fintype Λ] [Inhabited Λ]
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) :
  (generated_language (GenerationByTM0Simulation.TM_generator M
    (Λ := Λ)
    (Γ := Γ)
    (enc := (StandardEncoding Γ)))).val
  =
  (TM0_language M (Γ := Γ) (Λ := Λ)).val
 := by
  apply Set.Subset.antisymm
  · exact language_TM_generator_subset_language_TM0 M
  · exact language_TM0_subset_language_TM_generator M

theorem TM0_recognisable_subset_generable {Γ : Type u}
[Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ] :
TM0_recognisable_languages Γ ⊆ generable_languages := by
  intro L hL
  rcases hL with ⟨Λ, hΛinh, hΛfin, M, rfl⟩
  refine ⟨Γ, ?_⟩
  refine ⟨GenerationByTM0Simulation.GenState Λ Γ (StandardEncoding Γ), ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨inferInstance, ?_⟩
  refine ⟨GenerationByTM0Simulation.TM_generator M, ?_⟩
  apply Subtype.ext
  exact language_TM0_eq_language_TM_generator M

end RandomisedGeneration
