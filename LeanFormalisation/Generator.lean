import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine

def isRE {Γ : Type*} [Primcodable Γ] [Fintype Γ] (L : Set (List Γ)) : Prop :=
  REPred fun w ↦ w ∈ L

def reLanguages {Γ : Type*} [Primcodable Γ] [Fintype Γ] : Set (Set (List Γ)) :=
{ L | isRE L }

inductive Direction
  | L     -- move left
  | R     -- move right
  | N     -- stay / no move

instance : Coe Direction ℤ :=
⟨fun
  | Direction.L => -1
  | Direction.N => 0
  | Direction.R => 1⟩

inductive OneDirection
  | R     -- move right
  | N     -- stay / no move

instance : Coe OneDirection ℕ :=
⟨fun
  | OneDirection.N => 0
  | OneDirection.R => 1⟩

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
  δ : Q -> Bool -> Γw → Option (Q × Γw × Option Γo × OneDirection × Direction)


structure GeneratorConfiguration (Γw Γo Q : Type*) [Fintype Γw] [Fintype Γo] [Fintype Q] where
  (state : Q)
  (input : ℕ → Bool)
  (inputIndex : ℕ)
  (work : ℤ → Γw)
  (workIndex : ℤ)
  (output : List Γo)

def step {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q) (cfg : GeneratorConfiguration Γw Γo Q) :
  Option (GeneratorConfiguration Γw Γo Q) :=
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
  GeneratorConfiguration Γw Γo Q :=
{ state := gen.init
  input := input
  inputIndex := 0
  work := fun _ => gen.blank
  workIndex := 0
  output := []
}

def haltingConfig {Γw Γo Q} [Fintype Γw] [Fintype Γo] [Fintype Q]
  (gen : Generator Γw Γo Q)
  (cfg : GeneratorConfiguration Γw Γo Q) : Prop :=
step gen cfg = none

inductive computes {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q) (input : ℕ → Bool) : List Γo → Prop
  | halt (cfg : GeneratorConfiguration Γw Γo Q) :
      step gen cfg = none → computes gen input cfg.output
  | step (cfg cfg' : GeneratorConfiguration Γw Γo Q) (out : List Γo) :
      step gen cfg = some cfg' → computes gen input out → computes gen input out


def language {Γw Γo Q : Type*} [Fintype Γw] [Fintype Γo] [Fintype Q]
(gen : Generator Γw Γo Q) : Set (List Γo) :=
  { out | ∃ input, computes gen input out }

def generableLanguages {Γ : Type*} [Fintype Γ] : Set (Set (List Γ)) :=
{ L | ∃ (Γw Q : Type*) (_ : Fintype Γw) (_ : Fintype Q)
  (gen : Generator Γw Γ Q), language gen = L }

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
              OneDirection.R,
              Direction.L
            )
          | some (g : Γ) =>
            -- A symbol has been fully decoded. Write it to the work tape
            -- and produce it as an output. Reset the load state to start
            -- on the next symbol.
            some (
              GenState.load { bitsRead := 0, acc := 0, accBound := by simp},
              g,
              g,
              OneDirection.R,
              Direction.R
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
            OneDirection.R,
            Direction.N
          )
      | GenState.rewind =>
        if (w = (default : Γ)) then
          -- We have fully rewound, so proceed to simulation
          some (
            GenState.sim (default : Λ),
            w,
            none,
            OneDirection.N,
            Direction.R
          )
        else
          -- Not rewound far enough
          some (
            GenState.rewind,
            w,
            none,
            OneDirection.N,
            Direction.L
          )
      | GenState.sim q =>
        match M q w with
        | none => none
        | some (q', stmt) =>
          match stmt with
          | Turing.TM0.Stmt.write (g : Γ) =>
            some (GenState.sim q', g, none, OneDirection.N, Direction.N)
          | Turing.TM0.Stmt.move Turing.Dir.left =>
            some (GenState.sim q', w, none, OneDirection.N, Direction.L)
          | Turing.TM0.Stmt.move Turing.Dir.right =>
            some (GenState.sim q', w, none, OneDirection.N, Direction.R)
  }

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

theorem recognised_implies_generable {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
  {enc : Encoding Γ}
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom) :
  input ∈ language (TM_generator (enc := enc) M) := by
  sorry

theorem recognised_implies_generable_standard_encoding {Γ Λ : Type*}
  [Inhabited Λ] [Fintype Λ] [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (M : Turing.TM0.Machine (Γ := Γ) (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M input).Dom) :
  input ∈ language (TM_generator (enc := standardEncoding Γ) M) :=
    recognised_implies_generable M input h_halts
