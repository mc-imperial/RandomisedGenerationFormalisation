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

-- theorem TM0_recognisable_eq_RE {Γ : Type*} [Primcodable Γ] [Fintype Γ] [Inhabited Γ] :
--   TM0_recognisableLanguages Γ = reLanguages (Γ := Γ) := by
--   sorry

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

@[ext]
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

lemma StepsTo.refl {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg : GeneratorConfig Γw Γo Q} :
  StepsTo gen cfg cfg :=
by
  unfold StepsTo
  refine ⟨0, ?_⟩
  exact Steps.refl cfg

lemma StepsTo.trans {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q)
  {cfg1 cfg2 cfg3 : GeneratorConfig Γw Γo Q} :
  StepsTo gen cfg1 cfg2 → StepsTo gen cfg2 cfg3 → StepsTo gen cfg1 cfg3 :=
by
  rintro ⟨n, h1⟩ ⟨m, h2⟩
  exact ⟨n + m, Steps.trans h1 h2⟩

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
  W_pos : W > 0
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
            some (GenState.sim q', w, none, InputTapeDirection.N, WorkTapeDirection.R)
  }

namespace RecognisableEqualsGenerable

/-- Standard encoding using FinEnum, which provides a computable enumeration. -/
def standardEncoding (Γ : Type*) [Inhabited Γ] [FinEnum Γ] [DecidableEq Γ] : Encoding Γ where
  W := Nat.size (FinEnum.card Γ)
  W_pos := by
    -- Γ is inhabited, so card ≥ 1
    have h_card : FinEnum.card Γ ≥ 1 := by
      have : Nonempty Γ := ⟨default⟩
      exact FinEnum.card_pos
    -- Nat.size n > 0 for any n ≥ 1
    exact Nat.size_pos.mpr (Nat.pos_iff_ne_zero.mpr (by omega))
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
  fun i : ℕ => if h : i < input.length * enc.W then
    getEncodingBit enc (input.get ⟨i / enc.W, by
      exact Nat.div_lt_iff_lt_mul enc.W_pos |>.mpr h
    ⟩) (i % enc.W)
  else
    if i < (input.length + 1) * enc.W then
      getEOFBit enc (i % enc.W)
    else
      -- Bits after the encoding; value doesn't matter, so set them (arbitrarily) to false
      false

def readBlockBits (input : ℕ → Bool) (W k : ℕ) (x : Fin W) : ℕ :=
  (Finset.range x.val).sum (fun i =>
    (if input (k * W + i) then 1 else 0) * 2^(x.val - 1 - i))

lemma readBlockBits_succ {input : ℕ → Bool} {W k : ℕ} {x : ℕ} (hx : x + 1 < W) :
  readBlockBits input W k ⟨x + 1, hx⟩ =
    2 * readBlockBits input W k ⟨x, by omega⟩ + (if input (k * W + x) then 1 else 0) :=
by
  unfold readBlockBits
  simp only [add_tsub_cancel_right]
  rw [Finset.sum_range_succ]
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hx_pos : x > 0 := Nat.pos_of_ne_zero hx0
    calc (Finset.range x).sum (fun i => (if input (k * W + i) then 1 else 0) * 2 ^ (x - i)) +
         (if input (k * W + x) then 1 else 0) * 2 ^ (x - x)
        = (Finset.range x).sum (fun i => (if input (k * W + i) then 1 else 0) * 2 ^ (x - i)) +
          (if input (k * W + x) then 1 else 0) := by simp
      _ = (Finset.range x).sum (fun i =>
            2 * ((if input (k * W + i) then 1 else 0) * 2 ^ (x - 1 - i))) +
          (if input (k * W + x) then 1 else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            simp at hi
            have : x - i = (x - 1 - i) + 1 := by omega
            rw [this, pow_succ]
            ring
      _ = 2 * (Finset.range x).sum (fun i =>
          (if input (k * W + i) then 1 else 0) * 2 ^ (x - 1 - i)) +
          (if input (k * W + x) then 1 else 0) := by
            rw [← Finset.mul_sum]

lemma readBlockBits_lt_pow {input : ℕ → Bool} {W k : ℕ} {x : Fin W} (hW : W > 0) :
  readBlockBits input W k x < 2^W := by
  unfold readBlockBits
  by_cases hx : x.val = 0
  · simp [hx]
  · have hx_pos : x.val > 0 := Nat.pos_of_ne_zero hx
    calc (Finset.range x.val).sum (fun i =>
      (if input (k * W + i) then 1 else 0) * 2^(x.val - 1 - i))
        ≤ (Finset.range x.val).sum (fun i => 2^(x.val - 1 - i)) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs <;> simp
      _ < 2^x.val := by
          -- Sum of 2^(x-1) + 2^(x-2) + ... + 2^0 = 2^x - 1 < 2^x
          have : (Finset.range x.val).sum (fun i => 2^(x.val - 1 - i)) = 2^x.val - 1 := by
            sorry -- Geometric series
          rw [this]
          sorry
      _ ≤ 2^W := by
          apply Nat.pow_le_pow_right (by norm_num)
          exact Nat.le_of_lt x.isLt

lemma readBlockBits_le_pred_pow {input : ℕ → Bool} {W k : ℕ} {x : Fin W} (hW : W > 0)
    (hx : x.val ≤ W) :
  readBlockBits input W k x ≤ 2^x.val - 1 := by
  unfold readBlockBits
  by_cases hx0 : x.val = 0
  · simp [hx0]
  · have hx_pos : x.val > 0 := Nat.pos_of_ne_zero hx0
    -- Maximum is when all bits are 1
    calc (Finset.range x.val).sum (fun i =>
      (if input (k * W + i) then 1 else 0) * 2^(x.val - 1 - i))
        ≤ (Finset.range x.val).sum (fun i => 1 * 2^(x.val - 1 - i)) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs <;> simp
      _ = (Finset.range x.val).sum (fun i => 2^(x.val - 1 - i)) := by simp
      _ = 2^x.val - 1 := by
          -- Geometric series: 2^(n-1) + 2^(n-2) + ... + 2^0 = 2^n - 1
          sorry

lemma readBlockBits_decodes_to_symbol {Γ : Type*}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) {k : ℕ} (hk : k < input.length) :
  let W := (standardEncoding Γ).W
  let acc_val :=
    2 * readBlockBits (bitstreamFromInput input) W k ⟨W - 1, Nat.sub_lt
      (standardEncoding Γ).W_pos (by norm_num)⟩ +
                 (if bitstreamFromInput input (k * W + (W - 1)) then 1 else 0)
  ∃ (acc : Fin (2^W)) (h : acc.val = acc_val),
    (standardEncoding Γ).enum acc = some (input.get ⟨k, hk⟩) := by
  sorry

def DecodeBitInv {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  {k : ℕ} (hk : k ≤ input.length)
  {x : Fin (standardEncoding Γ).W} (hx : x.val < (standardEncoding Γ).W)
  : Prop :=
cfg.state = GenState.load {
    bitsRead := ⟨x.val, Nat.lt_succ_of_lt x.isLt⟩,
    acc := ⟨readBlockBits (bitstreamFromInput input)
      (standardEncoding Γ).W k x, readBlockBits_lt_pow (standardEncoding Γ).W_pos⟩
    accBound := readBlockBits_le_pred_pow (standardEncoding Γ).W_pos (Nat.le_of_lt hx)
  }
∧ cfg.inputIndex = k * (standardEncoding Γ).W + x.val
∧ cfg.workIndex = k
∧ (∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
∧ cfg.input = bitstreamFromInput input
∧ cfg.output = input.take k

def DecodeSymbolInv {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  {k : ℕ} (hk : k ≤ input.length)
   : Prop :=
  cfg.state = GenState.load  {
    bitsRead := 0,
    acc := 0,
    accBound := by simp }
  ∧ cfg.inputIndex = k * (standardEncoding Γ).W
  ∧ cfg.workIndex = k
  ∧ (∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
  ∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  ∧ cfg.input = bitstreamFromInput input
  ∧ cfg.output = input.take k

lemma decodeBitWithinSymbol {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  {k : ℕ} (hk : k ≤ input.length)
  {x : Fin (standardEncoding Γ).W} (hx : x.val < (standardEncoding Γ).W - 1)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (hinv : DecodeBitInv input cfg (k := k) (by omega) (x := x)
    (by exact Nat.lt_of_lt_pred hx)) :
  ∃ cfg',
    step (TM_generator (enc := standardEncoding Γ) M) cfg = some cfg' ∧
    DecodeBitInv input cfg' (k := k) (by omega) (x := ⟨x.val + 1, by omega⟩)
      (by omega) :=
by
  obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩ := hinv
  -- Show that step produces some configuration
  have h_step : ∃ cfg', step (TM_generator (enc := standardEncoding Γ) M) cfg = some cfg' := by
    simp only [step, TM_generator]
    rw [h_state, h_input, h_inputIndex, h_workIndex]
    have h_not_done : x.val ≠ (standardEncoding Γ).W := by omega
    simp [h_not_done]
  obtain ⟨cfg', h_step_eq⟩ := h_step
  use cfg'
  constructor
  · exact h_step_eq
  -- Now prove DecodeBitInv for cfg'
  simp only [step, TM_generator] at h_step_eq
  rw [h_state, h_input, h_inputIndex, h_workIndex] at h_step_eq
  have h_not_done : x.val ≠ (standardEncoding Γ).W := by omega
  simp only [h_not_done, ↓reduceDIte, Option.some.injEq] at h_step_eq
  subst h_step_eq
  constructor
  · -- State: GenState.load with updated values
    simp only [readBlockBits_succ]
  constructor
  · -- inputIndex
    ring
  constructor
  · -- workIndex
    rfl
  constructor
  · -- work tape for i < k
    intro i hi
    simp only
    have : i ≠ k := by omega
    simp only [Nat.cast_inj, this, ↓reduceIte, Int.toNat_natCast, List.get_eq_getElem]
    convert h_work_lt i hi
  constructor
  · -- work tape for i < 0 or k ≤ i
    intro i hi
    simp only
    split_ifs with heq
    · -- Case: i = k
      subst heq
      -- Now we need cfg.work k = default
      -- From hi: (k : ℤ) < 0 ∨ k ≤ (k : ℤ).toNat
      -- Since k : ℕ, we have (k : ℤ).toNat = k and (k : ℤ) ≮ 0
      apply h_work_ge
      right
      simp
    · -- Case: i ≠ k
      -- Need cfg.work i = default, which follows from h_work_ge and hi
      exact h_work_ge i hi
  constructor
  · -- input
    rfl
  · -- output
    simp only
    exact h_output

lemma decodeBitFinal {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  {k : ℕ} (hk : k < input.length)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (hinv : DecodeBitInv input cfg (k := k) (by omega)
    (x := ⟨(standardEncoding Γ).W - 1, Nat.sub_lt (standardEncoding Γ).W_pos (by norm_num)⟩)
    (Nat.sub_lt (standardEncoding Γ).W_pos (by norm_num))) :
  ∃ (cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
    (acc : Fin (2 ^ (standardEncoding Γ).W)),
    step (TM_generator (enc := standardEncoding Γ) M) cfg = some cfg' ∧
    (standardEncoding Γ).enum acc = some (input.get ⟨k, hk⟩) ∧
    cfg'.state = GenState.load {
      bitsRead := ⟨(standardEncoding Γ).W, by omega⟩,
      acc := acc,
      accBound := by simp; omega
    } ∧
    cfg'.inputIndex = (k + 1) * (standardEncoding Γ).W ∧
    cfg'.workIndex = k ∧
    (∀ i (hi : i < k), cfg'.work i = input.get ⟨Int.toNat i, by omega⟩) ∧
    (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg'.work i = default) ∧
    cfg'.input = bitstreamFromInput input ∧
    cfg'.output = input.take k :=
by sorry

lemma decodeSymbolWrite {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  {k : ℕ} (hk : k < input.length)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (acc : Fin (2 ^ (standardEncoding Γ).W))
  (h_state : cfg.state = GenState.load {
    bitsRead := ⟨(standardEncoding Γ).W, by omega⟩,
    acc := acc,
    accBound := by simp; omega
  })
  (h_enum : (standardEncoding Γ).enum acc = some (input.get ⟨k, hk⟩))
  (h_inputIndex : cfg.inputIndex = (k + 1) * (standardEncoding Γ).W)
  (h_workIndex : cfg.workIndex = k)
  (h_work_lt : ∀ i (hi : i < k), cfg.work i = input.get ⟨Int.toNat i, by omega⟩)
  (h_work_ge : ∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  (h_input : cfg.input = bitstreamFromInput input)
  (h_output : cfg.output = input.take k) :
  ∃ cfg',
    step (TM_generator (enc := standardEncoding Γ) M) cfg = some cfg' ∧
    DecodeSymbolInv input cfg' (k := k + 1) (by omega) :=
by sorry

-- Decode the final bit of the EOF marker, triggering rewind
lemma decodeEOFBitFinal {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (hinv : DecodeBitInv input cfg (k := input.length) (by omega)
    (x := ⟨(standardEncoding Γ).W - 1, Nat.sub_lt (standardEncoding Γ).W_pos (by norm_num)⟩)
    (Nat.sub_lt (standardEncoding Γ).W_pos (by norm_num))) :
  ∃ cfg',
    step (TM_generator (enc := standardEncoding Γ) M) cfg = some cfg' ∧
    cfg'.state = GenState.rewind ∧
    cfg'.workIndex = input.length - 1 ∧
    (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩) ∧
    (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = default) ∧
    (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = default) ∧
    cfg'.output = input
:= by sorry

lemma decodeOneSymbol {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  {k : ℕ} (hk : k < input.length)
: DecodeSymbolInv input cfg (k := k) (by omega) → ∃ cfg',
  StepsTo (TM_generator (enc := standardEncoding Γ) M) cfg cfg'
  ∧ DecodeSymbolInv input cfg' (k := k + 1) (by omega)
:= by
  intro h_DecodeSymbolInv
  let W := (standardEncoding Γ).W
  have hW : W > 0 := (standardEncoding Γ).W_pos
  -- Separate helper with explicit measure
  have decode_from_bit_aux :
      ∀ (n : ℕ) (i : ℕ) (hi : i < W) (hn : n = W - 1 - i)
        (cfg_i : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ))),
      DecodeBitInv input cfg_i (k := k) (by omega) (x := ⟨i, hi⟩) (by exact hi) →
      ∃ cfg',
        StepsTo (TM_generator (enc := standardEncoding Γ) M) cfg_i cfg' ∧
        DecodeSymbolInv input cfg' (k := k + 1) (by omega) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi hn cfg_i h_inv
      by_cases h_last : i = W - 1
      · -- Last bit: need TWO steps now (decodeBitFinal + decodeSymbolWrite)
        subst h_last
        -- First step: accumulate final bit
        obtain ⟨cfg_mid, acc, h_step1, h_enum, h_state_mid, h_inputIndex_mid,
          h_workIndex_mid, h_work_lt_mid, h_work_ge_mid, h_input_mid, h_output_mid⟩ :=
          decodeBitFinal M input hk cfg_i h_inv
        -- Second step: decode and write symbol
        obtain ⟨cfg', h_step2, h_next⟩ :=
          decodeSymbolWrite M input hk cfg_mid acc h_state_mid h_enum
            h_inputIndex_mid h_workIndex_mid h_work_lt_mid h_work_ge_mid
            h_input_mid h_output_mid
        refine ⟨cfg', ?_, h_next⟩
        -- Construct 2 steps
        have h_steps : Steps (TM_generator (enc := standardEncoding Γ) M) cfg_i cfg' 2 := by
          apply Steps.step cfg_i cfg_mid cfg' 1 h_step1
          exact Steps.step cfg_mid cfg' cfg' 0 h_step2 (Steps.refl cfg')
        exact ⟨2, h_steps⟩
      · -- Not last bit
        have h_i_lt : i < W - 1 := by omega
        have hk_le : k ≤ input.length := by omega
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decodeBitWithinSymbol M input hk_le h_i_lt cfg_i h_inv
        have h_i_succ : i + 1 < W := by omega
        have hn_next : n - 1 = W - 1 - (i + 1) := by omega
        have h_n_pos : 0 < n := by omega
        obtain ⟨cfg', h_steps_rest, h_final⟩ :=
          ih (n - 1) (by omega) (i + 1) h_i_succ hn_next cfg_next h_next_inv
        refine ⟨cfg', ?_, h_final⟩
        exact StepsTo.trans _
          ⟨1, Steps.step cfg_i cfg_next cfg_next 0 h_step (Steps.refl cfg_next)⟩
          h_steps_rest
  have h_start : DecodeBitInv input cfg (k := k) (by omega)
      (x := ⟨0, hW⟩) (by exact hW) := by
    obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge,
      h_input, h_output⟩ := h_DecodeSymbolInv
    refine ⟨h_state, ?_, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩
    simp [h_inputIndex]
  exact decode_from_bit_aux (W - 1) 0 hW rfl cfg h_start

lemma decodeFinalSymbol {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (h_ready_for_last_symbol : DecodeSymbolInv input cfg (k := input.length) (by omega))
: ∃ cfg',
StepsTo (TM_generator (enc := standardEncoding Γ) M) cfg cfg'
∧ (
  cfg'.state = GenState.rewind
∧ cfg'.workIndex = input.length - 1
∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
∧ cfg'.output = input
) := by
  let W := (standardEncoding Γ).W
  have hW : W > 0 := (standardEncoding Γ).W_pos
  -- Helper with explicit measure
  have decode_eof_from_bit :
      ∀ (n : ℕ) (i : ℕ) (hi : i < W) (hn : n = W - 1 - i)
        (cfg_i : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ))),
      DecodeBitInv input cfg_i (k := input.length) (by omega)
        (x := ⟨i, hi⟩) (by exact hi) →
      ∃ cfg',
        StepsTo (TM_generator (enc := standardEncoding Γ) M) cfg_i cfg' ∧
        cfg'.state = GenState.rewind ∧
        cfg'.workIndex = input.length - 1 ∧
        (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩) ∧
        (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ)) ∧
        (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ)) ∧
        cfg'.output = input := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi hn cfg_i h_inv
      by_cases h_last : i = W - 1
      · -- Last bit: use decodeEOFBitFinal
        subst h_last
        obtain ⟨cfg', h_step, h_rewind, h_workIndex, h_work_lt, h_work_ge,
          h_work_neg, h_output⟩ := decodeEOFBitFinal M input cfg_i h_inv
        refine ⟨cfg', ?_, h_rewind, h_workIndex, h_work_lt, h_work_ge,
          h_work_neg, h_output⟩
        exact ⟨1, Steps.step cfg_i cfg' cfg' 0 h_step (Steps.refl cfg')⟩
      · -- Not last bit: use decodeBitWithinSymbol
        have h_i_lt : i < W - 1 := by omega
        have hk_le : input.length ≤ input.length := by omega
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decodeBitWithinSymbol M input hk_le h_i_lt cfg_i h_inv
        have h_i_succ : i + 1 < W := by omega
        have hn_next : n - 1 = W - 1 - (i + 1) := by omega
        have h_n_pos : 0 < n := by omega
        obtain ⟨cfg', h_steps_rest, h_rewind, h_workIndex, h_work_lt, h_work_ge,
          h_work_neg, h_output⟩ :=
          ih (n - 1) (by omega) (i + 1) h_i_succ hn_next cfg_next h_next_inv
        refine ⟨cfg', ?_, h_rewind, h_workIndex, h_work_lt, h_work_ge,
          h_work_neg, h_output⟩
        exact StepsTo.trans _
          ⟨1, Steps.step cfg_i cfg_next cfg_next 0 h_step (Steps.refl cfg_next)⟩
          h_steps_rest
  -- Convert DecodeSymbolInv to DecodeBitInv at bit 0
  have h_start : DecodeBitInv input cfg (k := input.length) (by omega)
      (x := ⟨0, hW⟩) (by exact hW) := by
    obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge,
      h_input, h_output⟩ := h_ready_for_last_symbol
    refine ⟨h_state, ?_, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩
    simp [h_inputIndex]
  -- Apply the helper to bit 0
  exact decode_eof_from_bit (W - 1) 0 hW rfl cfg h_start

lemma weGetReadyToRewind {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
: ∃ cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)),
    let gen := TM_generator (enc := standardEncoding Γ) M
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
  set gen := TM_generator (enc := standardEncoding Γ) M
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
      ∃ cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)),
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
        decodeOneSymbol M input cfg_i h_lt hInv_i
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
  obtain ⟨cfg_final, h_properties_of_cfg_final⟩ := decodeFinalSymbol M input cfg_all_decoded
    h_inv_all_decoded
  rcases h_properties_of_cfg_final with
    ⟨h_steps_cfg_final, h_state_cfg_final, h_workIndex_cfg_final, h_work_lt_cfg_final,
     h_work_ge_cfg_final, h_work_neg_cfg_final, h_output_cfg_final⟩
  use cfg_final
  have h_initial_stepsto_final :
    StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg_final :=
      StepsTo.trans gen h_initial_steps_to_cfg_all_decoded h_steps_cfg_final
  refine ⟨h_state_cfg_final,
        h_workIndex_cfg_final,
        h_work_lt_cfg_final,
        h_work_ge_cfg_final,
        h_work_neg_cfg_final,
        h_output_cfg_final,
        h_initial_stepsto_final⟩

lemma rewindWithNonNegativeIndexOneStep {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ default ∉ input)
: step (TM_generator (enc := standardEncoding Γ) M) cfg = some {
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

lemma rewindWithNonNegativeIndexManySteps {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := TM_generator (enc := standardEncoding Γ) M
    cfg'.state = GenState.rewind
    ∧ cfg'.workIndex = -1
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := TM_generator (enc := standardEncoding Γ) M
  obtain ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_work_ge,
          h_work_neg, h_output, h_no_blank⟩ := h
  -- Induction on cfg.workIndex.toNat
  match n : cfg.workIndex.toNat with
  | 0 =>
    -- Base case: cfg.workIndex = 0
    have h_idx_eq : cfg.workIndex = 0 := by omega
    -- Take one step to get to workIndex = -1
    let cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)) := {
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
    let cfg_next : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)) := {
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

lemma rewindWithNegativeIndex {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = -1
    ∧ cfg.work (-1) = (default : Γ))
: step (TM_generator (enc := standardEncoding Γ) M) cfg = some {
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

lemma rewindingLeadsToSimulationReadiness {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = input.length - 1
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := TM_generator (enc := standardEncoding Γ) M
    cfg'.state = GenState.sim (default : Λ)
    ∧ cfg'.workIndex = 0
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = input.get ⟨i, h⟩)
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := TM_generator (enc := standardEncoding Γ) M
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low, h_output, h_nodefault⟩
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
         h_work_blank_high, h_work_blank_low, h_output, h_nodefault⟩
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output,
            h_steps_to_rewind⟩ :=
      rewindWithNonNegativeIndexManySteps M input cfg h_many_conditions
    have h_rewind_work_neg : rewindCfg.work (-1) = default :=
      h_rewind_work_blank_low (-1) (by omega)
    have h_step := rewindWithNegativeIndex M rewindCfg
      ⟨h_rewind_state, h_rewind_idx, h_rewind_work_neg⟩
    let finalCfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)) := {
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

lemma weGetReadyToSimulate {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_nodefault : default ∉ input)
: ∃ cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)),
    let gen := TM_generator (enc := standardEncoding Γ) M
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
    let gen := TM_generator (enc := standardEncoding Γ) M
    -- First, get to the rewind state
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_init_to_rewind⟩ :=
      weGetReadyToRewind M input
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
               h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_nodefault⟩
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

structure configurationsMatch {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (genCfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ Λ) : Prop where
  states_match : genCfg.state = GenState.sim (Λ := Λ) (Γ := Γ) (enc := standardEncoding Γ) tm0Cfg.q
  heads_match : genCfg.work genCfg.workIndex = tm0Cfg.Tape.head
  tape_match_right : ∀ (d : ℕ), genCfg.work (genCfg.workIndex + 1 + d) =
    Turing.ListBlank.nth tm0Cfg.Tape.right d
  tape_match_left : ∀ (d : ℕ), genCfg.work (genCfg.workIndex - 1 - d) =
    Turing.ListBlank.nth tm0Cfg.Tape.left d

def maybeConfigurationsMatch {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (maybeGenCfg : Option (GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ))))
  (maybeTm0Cfg : Option (Turing.TM0.Cfg Γ Λ)) : Prop :=
match maybeGenCfg, maybeTm0Cfg with
| none, none => True
| some genCfg, some tm0Cfg => configurationsMatch genCfg tm0Cfg
| _, _ => False

lemma matchingConfigurationsStepSimultaneously {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine Γ Λ)
  (genCfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
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

lemma simStaysInSimAndPreservesOutput {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (cfg cfg' : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
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

lemma simulationWorksOnceWeAreReady {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom)
  (cfg : GeneratorConfig Γ Γ (GenState Λ Γ (standardEncoding Γ)))
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
    let gen := TM_generator (enc := standardEncoding Γ) M
    StepsTo gen cfg haltCfg
    ∧ haltingConfig gen haltCfg
    ∧ haltCfg.output = input := by
  --
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low,
    h_output, h_nodefault⟩ := h_cfg
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
        let gen := TM_generator (enc := standardEncoding Γ) M
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
      (TM_generator (enc := standardEncoding Γ) M) haltCfg := by
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

theorem recognised_implies_generable {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_nodefault : default ∉ input)
  (h_halts : (Turing.TM0.eval M input).Dom) :
  input ∈ generatedLanguage (TM_generator (enc := standardEncoding Γ) M) := by
    let enc := standardEncoding Γ
    let gen := (TM_generator (enc := enc) M)
    rcases weGetReadyToSimulate M input h_nodefault
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
              h_readyCfg_work_tape_blank_below, h_readyCfg_output_is_input, h_nodefault⟩
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

end RecognisableEqualsGenerable
