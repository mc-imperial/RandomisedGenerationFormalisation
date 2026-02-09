import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine

def isRE {Γ : Type*} [Primcodable Γ] [Fintype Γ] (L : Set (List Γ)) : Prop :=
  REPred fun w ↦ w ∈ L

def reLanguages {Γ : Type*} [Primcodable Γ] [Fintype Γ] : Set (Set (List Γ)) :=
{ L | isRE L }

def TM0_language {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)) : Set (List Γ) :=
  { input | (Turing.TM0.eval M input).Dom }

def TM0_recognisableLanguages (Γ : Type*) [Inhabited Γ] : Set (Set (List Γ)) :=
  { L | ∃ (Λ : Type*) (_ : Inhabited Λ) (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ)),
    L = TM0_language M }

theorem TM0_recognisable_eq_RE {Γ : Type*} [Primcodable Γ] [Fintype Γ] [Inhabited Γ] :
  TM0_recognisableLanguages Γ = reLanguages (Γ := Γ) := by
  sorry

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
structure Generator (Γw Γo Q : Type*) [Fintype Γw] [Fintype Γo] [Fintype Q] where
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


structure GeneratorConfig (Γw Γo Q : Type*) [Fintype Γw] [Fintype Γo] [Fintype Q] where
  (state : Q)
  (input : ℕ → Bool)
  (inputIndex : ℕ)
  (work : ℤ → Γw)
  (workIndex : ℤ)
  (output : List Γo)

def step {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
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

def initConfig {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q) (input : ℕ → Bool) :
  GeneratorConfig Γw Γo Q :=
{ state := gen.init
  input := input
  inputIndex := 0
  work := fun _ => gen.blank
  workIndex := 0
  output := []
}

def haltingConfig {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q)
  (cfg : GeneratorConfig Γw Γo Q) : Prop :=
step gen cfg = none

inductive Computes {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q) : GeneratorConfig Γw Γo Q → List Γo → Prop
  | halt (cfg : GeneratorConfig Γw Γo Q) :
      step gen cfg = none → Computes gen cfg cfg.output
  | step (cfg cfg' : GeneratorConfig Γw Γo Q) (out : List Γo) :
      step gen cfg = some cfg' → Computes gen cfg' out → Computes gen cfg out

inductive Steps {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
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

lemma Steps.trans {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
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

def StepsTo {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q)
(cfg : GeneratorConfig Γw Γo Q)
(cfg' : GeneratorConfig Γw Γo Q) : Prop :=
  ∃ n, Steps gen cfg cfg' n

def HaltsFrom {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q)
(cfg : GeneratorConfig Γw Γo Q) : Prop :=
  ∃ cfg' n,
    Steps gen cfg cfg' n ∧
    haltingConfig gen cfg'

-- Helper lemma: if we step to a halting config, then we compute its output
lemma StepsTo.computes {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
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

def generatedLanguage {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q) : Set (List Γo) :=
  { out | ∃ input, Computes gen (initConfig gen input) out }

def generableLanguages {Γ : Type*} [Fintype Γ] : Set (Set (List Γ)) :=
{ L | ∃ (Γw Q : Type*) (_ : Fintype Γw) (_ : Fintype Q)
  (gen : Generator Γw Γ Q), generatedLanguage gen = L }

-- lemma generableLanguages_subset_reLanguages {Γ : Type*} [Primcodable Γ] [Fintype Γ]
-- : generableLanguages (Γ := Γ) ⊆ reLanguages (Γ := Γ) := by sorry

-- lemma reLanguages_subset_generableLanguages {Γ : Type*} [Primcodable Γ] [Fintype Γ]
-- : reLanguages (Γ := Γ) ⊆ generableLanguages (Γ := Γ) := by sorry

-- theorem generatebleLanguages_eq_reLanguages {Γ : Type*} [Primcodable Γ] [Fintype Γ]
-- : generableLanguages (Γ := Γ) = reLanguages (Γ := Γ) := by
--   exact
--     Set.Subset.antisymm generableLanguages_subset_reLanguages
--       reLanguages_subset_generableLanguages

structure Encoding (Γ : Type*) where
  W : ℕ
  enum : Fin (2^W) → Option Γ
  complete : ∀ g : Γ, ∃ i, enum i = some g

structure LoadState (Γ : Type*) (enc : Encoding Γ) where
  bitsRead : Fin (enc.W + 1)      -- 0 .. W
  acc      : Fin (2 ^ enc.W)      -- fixed width accumulator
  accBound : acc.val ≤ 2 ^ bitsRead.val - 1 -- invariant
deriving Fintype

inductive GenState (Λ Γ : Type*) [Fintype Λ] [Fintype Γ] [Inhabited Γ]
  (enc : Encoding Γ) where
  | load (ls : LoadState Γ enc)
  | rewind
  | sim  (q  : Λ)
deriving Fintype

def TM_generator {Γ Λ : Type*}
  [Inhabited Λ]
  [Fintype Λ]
  [Inhabited Γ]
  [Fintype Γ]
  [DecidableEq Γ]
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
              InputTapeDirection.R,
              WorkTapeDirection.L
            )
          | some (g : Γ) =>
            -- A symbol has been fully decoded. Write it to the work tape
            -- and produce it as an output. Reset the load state to start
            -- on the next symbol.
            some (
              GenState.load { bitsRead := 0, acc := 0, accBound := by simp},
              g,
              g,
              InputTapeDirection.R,
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
            some (GenState.sim q', w, none, InputTapeDirection.N, WorkTapeDirection.R)
  }

namespace RecognisableEqualsGenerable

/-- Standard encoding using FinEnum, which provides a computable enumeration. -/
def standardEncoding (Γ : Type*) [FinEnum Γ] [DecidableEq Γ] : Encoding Γ where
  W := Nat.size (FinEnum.card Γ)
  enum := fun (i : Fin (2^(Nat.size (FinEnum.card Γ)))) =>
    if h : i < FinEnum.card Γ then
      some (FinEnum.equiv.symm ⟨i.val, h⟩)
    else
      none
  complete := by
    intro g
    let idx := FinEnum.equiv g
    -- Now reason that this will take the "then" branch of enum
    use ⟨idx.val, by
      calc idx.val
          < FinEnum.card Γ := idx.isLt
        _ < 2 ^ Nat.size (FinEnum.card Γ) := Nat.lt_size_self (FinEnum.card Γ)
    ⟩
    simp [idx]

-- Helper function to get the i-th bit of a natural number in MSB-first order
-- For a W-bit encoding, bit 0 is the most significant, bit W-1 is the least significant
def getNthBitMSB (n : ℕ) (width : ℕ) (i : ℕ) : Bool :=
  if i < width then
    n.testBit (width - 1 - i)
  else
    false

-- Encode a symbol as its index in the finite enumeration
def symbolToNat {Γ : Type*} [FinEnum Γ] (g : Γ) : ℕ :=
  (FinEnum.equiv g).val

-- Get the k-th bit of the encoding of symbol g (MSB-first)
def getEncodingBit {Γ : Type*} [FinEnum Γ] (enc : Encoding Γ) (g : Γ) (k : ℕ) : Bool :=
  getNthBitMSB (symbolToNat g) enc.W k

-- The special "end of input" encoding
def getEOFBit {Γ : Type*} [Fintype Γ] (enc : Encoding Γ) (k : ℕ) : Bool :=
  getNthBitMSB (Fintype.card Γ) enc.W k

def bitstreamFromInput {Γ : Type*} [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
 (input : List Γ) : ℕ → Bool :=
  let enc := standardEncoding Γ
  fun i : ℕ => if i < input.length * enc.W then
    getEncodingBit enc (input.get ⟨i / enc.W, sorry⟩) (i % enc.W)
  else
    if i < (input.length + 1) * enc.W then
      getEOFBit enc (i % enc.W)
    else
      -- Bits after the encoding; value doesn't matter, so set them (arbitrarily) to false
      false

lemma simulationWorksOnceWeAreReady {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
: cfg.state = GenState.sim (default : Λ)
  ∧ cfg.workIndex = 0
  ∧ (∀ i (h : i < input.length),
      cfg.work (i : ℤ) = input.get ⟨i, h⟩)
  ∧ (∀ i : ℕ, i ≥ input.length →
      cfg.work (i : ℤ) = (default : Γ))
  ∧ cfg.output = input
  → ∃ haltCfg,
    let gen := TM_generator (enc := standardEncoding Γ) M
    StepsTo gen cfg haltCfg
    ∧ haltingConfig gen haltCfg
    ∧ haltCfg.output = input := by sorry

lemma weGetReadyToSimulate {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom)
: ∃ cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)),
    let gen := TM_generator (enc := standardEncoding Γ) M
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < input.length),
        cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length →
        cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg := by sorry

theorem recognised_implies_generable {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom) :
  input ∈ generatedLanguage (TM_generator (enc := standardEncoding Γ) M) := by
    let enc := standardEncoding Γ
    let gen := (TM_generator (enc := enc) M)
    rcases weGetReadyToSimulate M input h_halts
      with ⟨
        readyCfg,
        h_readyCfg_initial_state,
        h_readyCfg_work_index_zero,
        h_readyCfg_work_tape_contains_input,
        h_readyCfg_work_tape_blank_elsewhere,
        h_readyCfg_output_is_input,
        h_initial_stepsTo_readyCfg
      ⟩
    -- Build the hypothesis needed for simulationWorksOnceWeAreReady
    have h_ready : readyCfg.state = GenState.sim (default : Λ)
      ∧ readyCfg.workIndex = 0
      ∧ (∀ i (h : i < input.length), readyCfg.work (i : ℤ) = input.get ⟨i, h⟩)
      ∧ (∀ i : ℕ, i ≥ input.length → readyCfg.work (i : ℤ) = (default : Γ))
      ∧ readyCfg.output = input := by
        exact ⟨h_readyCfg_initial_state, h_readyCfg_work_index_zero,
               h_readyCfg_work_tape_contains_input, h_readyCfg_work_tape_blank_elsewhere,
               h_readyCfg_output_is_input⟩
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


-- WIP
lemma eatOneInputBit {Λ Γ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (i : ℕ)
  : ∃ ls : LoadState Γ (standardEncoding Γ), cfg.state = GenState.load ls
      ∧ ls.bitsRead < (standardEncoding Γ).W - 1 → false := by sorry

-- hready : have gen := TM_generator M;
-- readyCfg.state = GenState.sim default ∧
--   readyCfg.workIndex = 0 ∧
--     (∀ (i : ℕ) (h : i < input.length), readyCfg.work ↑i = input.get ⟨i, h⟩) ∧
--       (∀ i ≥ input.length, readyCfg.work ↑i = default) ∧
--         readyCfg.output = input ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) readyCfg

    -- have htotal : StepsTo gen (initConfig gen (bitstreamFromInput input)) haltCfg := by sorry
    -- have hcomputes : Computes gen (initConfig gen (bitstreamFromInput input)) haltCfg.output :=
    --   stepsTo_halts_implies_computes gen _ _ htotal hsim.2
    -- exact ⟨bitstreamFromInput input, by
    --   rw [hsim.3]; exact hcomputes⟩
    sorry

end RecognisableEqualsGenerable
