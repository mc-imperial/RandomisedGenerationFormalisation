import Mathlib
import Mathlib.Computability.Halting
import Mathlib.Computability.PostTuringMachine
import RandomisedGeneration.Encoding
import RandomisedGeneration.Generator
import RandomisedGeneration.Language

namespace RandomisedGeneration

namespace GenerationByTM0Simulation

structure LoadState (Γ : Type u) (enc_Γ : Encoding Γ) where
  bitsRead : Fin (enc_Γ.W + 1)      -- 0 .. W
  acc      : Fin (2 ^ enc_Γ.W)      -- fixed width accumulator
  accBound : acc.val ≤ 2 ^ bitsRead.val - 1 -- invariant
deriving Fintype

inductive GenState (Λ Γ : Type u)
[Inhabited Γ] [FinEnum Γ]
  (enc_Γ : Encoding Γ) where
  | load (ls : LoadState Γ enc_Γ)
  | rewind
  | sim  (q  : Λ)


def generatorFromTM0 {Γ Γ' Λ : Type u}
    [Inhabited Λ]
    [Inhabited Γ] [FinEnum Γ]
    [Inhabited Γ'] [FinEnum Γ']
    {enc_Γ : Encoding Γ}
    (change_of_alphabet : Γ → Γ')
    (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
    : Generator (Γw := Γ') (Γo := Γ) (Q := GenState Λ Γ enc_Γ) :=
  {
    init := GenState.load {bitsRead := 0, acc := 0, accBound := by simp},
    blank := (default : Γ'),
    δ := fun state b (w : Γ') =>
      match state with
      | GenState.load ls =>
        if h_eq : ls.bitsRead.val = enc_Γ.W then
          -- done reading, produce a symbol
          match enc_Γ.enum ls.acc with
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
                change_of_alphabet g,
                g,
                InputTapeDirection.N,
                WorkTapeDirection.R
              )
        else
          let newBits : Fin (enc_Γ.W + 1) := ⟨ls.bitsRead.val + 1, by omega⟩
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
          have h_newAcc_bound : 2 * ls.acc.val + (if b then 1 else 0) < 2 ^ enc_Γ.W := by
            have h_bitsRead_lt_W : ls.bitsRead.val < enc_Γ.W := by omega
            have : 2 ^ (ls.bitsRead.val + 1) ≤ 2 ^ enc_Γ.W :=
              Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h_bitsRead_lt_W)
            have : 2 * 2 ^ ls.bitsRead.val = 2 ^ (ls.bitsRead.val + 1) := by ring
            omega
          --
          let newAcc : Fin (2^enc_Γ.W) := ⟨2 * ls.acc.val + if b then 1 else 0, h_newAcc_bound⟩
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
        if (w = (default : Γ')) then
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
          | Turing.TM0.Stmt.write (g : Γ') =>
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
        · -- bitsRead.val = enc_Γ.W
          split at h_δ
          · -- enc_Γ.enum ls.acc = none
            simp only [Option.some.injEq] at h_δ
            obtain ⟨_, _, h_o_eq, _, _⟩ := h_δ
            simp at h_o
          · -- enc_Γ.enum ls.acc = some g
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
        · -- bitsRead.val ≠ enc_Γ.W
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

def decode_bit_inv {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
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
∧ (∀ i (hi : i < k), cfg.work i = change_of_alphabet (input.get ⟨Int.toNat i, by omega⟩))
∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
∧ cfg.input = bitstreamFromInput input
∧ cfg.output = input.take k

def decode_symbol_inv {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  {k : ℕ} (hk : k ≤ input.length)
  : Prop :=
  cfg.state = GenState.load {
    bitsRead := 0,
    acc := 0,
    accBound := by simp }
  ∧ cfg.inputIndex = k * (StandardEncoding Γ).W
  ∧ cfg.workIndex = k
  ∧ (∀ i (hi : i < k), cfg.work i = change_of_alphabet (input.get ⟨Int.toNat i, by omega⟩))
  ∧ (∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  ∧ cfg.input = bitstreamFromInput input
  ∧ cfg.output = input.take k

lemma decode_bit_within_symbol {Γ Γ' Λ : Type u}
  [Inhabited Λ]
  [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  {k : ℕ} (hk : k ≤ input.length)
  (x : Fin (WIDTH Γ))
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (hinv : decode_bit_inv change_of_alphabet input cfg (k := k) (by omega)
    ⟨x, Nat.lt_succ_of_lt x.isLt⟩) :
  ∃ cfg',
    step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg = some cfg' ∧
    decode_bit_inv change_of_alphabet input cfg' (k := k) (by omega) ⟨x.val + 1, by omega⟩ := by
  obtain ⟨h_state, h_inputIndex, h_workIndex, h_work_lt, h_work_ge, h_input, h_output⟩ := hinv
  -- Simplify step to get concrete configuration
  simp only [step, generatorFromTM0]
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

lemma write_decoded_symbol {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  {k : ℕ} (hk : k < input.length)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (acc : Fin (2 ^ (StandardEncoding Γ).W))
  (h_state : cfg.state = GenState.load {
    bitsRead := ⟨(StandardEncoding Γ).W, by omega⟩,
    acc := acc,
    accBound := by simp; omega
  })
  (h_enum : (StandardEncoding Γ).enum acc = some (input.get ⟨k, hk⟩))
  (h_inputIndex : cfg.inputIndex = (k + 1) * (StandardEncoding Γ).W)
  (h_workIndex : cfg.workIndex = k)
  (h_work_lt : ∀ i (hi : i < k), cfg.work i =
    change_of_alphabet (input.get ⟨Int.toNat i, by omega⟩))
  (h_work_ge : ∀ i : ℤ, i < 0 ∨ k ≤ Int.toNat i → cfg.work i = default)
  (h_input : cfg.input = bitstreamFromInput input)
  (h_output : cfg.output = input.take k) :
  ∃ cfg',
    step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg = some cfg' ∧
    decode_symbol_inv change_of_alphabet input cfg' (k := k + 1) (by omega) := by
  -- Unfold step and generatorFromTM0
  simp only [step, generatorFromTM0]
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
    work := fun i => if i = cfg.workIndex then
      change_of_alphabet (input.get ⟨k, hk⟩) else cfg.work i,
    workIndex := cfg.workIndex + 1,
    output := cfg.output ++ [input.get ⟨k, hk⟩]
  }
  constructor
  · simp only [List.get_eq_getElem, h_enum, List.get_eq_getElem, Int.reduceNeg,
      h_inputIndex, h_workIndex]
    have h_get_eq : input[k] = input.get ⟨k, hk⟩ := by rfl
    rw [h_get_eq]
    simp only [h_not_default, ↓reduceIte, add_zero]
  -- Prove decode_symbol_inv
  unfold decode_symbol_inv
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

lemma decode_one_symbol {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  {k : ℕ} (hk : k < input.length)
:
  decode_symbol_inv change_of_alphabet input cfg (k := k) (by omega) →
  ∃ cfg',
    StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfg' ∧
    decode_symbol_inv change_of_alphabet input cfg' (k := k + 1) (by omega)
:= by
  intro h_sym
  let W := (StandardEncoding Γ).W
  have hWpos : W > 0 := (StandardEncoding Γ).W_pos
  -- Convert decode_symbol_inv → decode_bit_inv at x = 0
  have h_bit0 :
    decode_bit_inv change_of_alphabet input cfg (k := k) (by omega)
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
      StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfgW ∧
      decode_bit_inv change_of_alphabet input cfgW (k := k) (by omega)
        ⟨W, by linarith⟩ :=
  by
    -- Induction on natural x < W
    have :
      ∀ x : ℕ, (hx : x ≤ W) →
        ∃ cfgx,
          StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfgx ∧
          decode_bit_inv change_of_alphabet input cfgx (k := k) (by omega)
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
        -- Now show x < W so we can use decode_bit_within_symbol
        have hx_lt : x < W := by
          exact Nat.lt_of_succ_le hx
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decode_bit_within_symbol
            change_of_alphabet M input
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
  -- Extract the necessary components from decode_bit_inv at W
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
    write_decoded_symbol change_of_alphabet M input h_no_default hk
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

lemma detect_EOF {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (acc : Fin (2 ^ (StandardEncoding Γ).W))
  (h_state : cfg.state = GenState.load {
    bitsRead := ⟨(StandardEncoding Γ).W, by omega⟩,
    acc := acc,
    accBound := by simp; omega
  })
  (h_enum : (StandardEncoding Γ).enum acc = none)
  :
  ∃ cfg',
    step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg = some cfg' ∧
    cfg'.state = GenState.rewind ∧
    cfg'.inputIndex = cfg.inputIndex ∧
    cfg'.workIndex = cfg.workIndex - 1 ∧
    cfg'.work = cfg.work ∧
    cfg'.output = cfg.output
:= by
  -- Unfold step and generatorFromTM0
  simp only [step, generatorFromTM0]
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

lemma decode_EOF_marker {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_ready_for_last_symbol : decode_symbol_inv change_of_alphabet input cfg
    (k := input.length) (by omega))
: ∃ cfg',
StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfg'
∧ (
  cfg'.state = GenState.rewind
∧ cfg'.workIndex = cfg.workIndex - 1
∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ'))
∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ'))
∧ cfg'.output = input
) := by
  let W := (StandardEncoding Γ).W
  have hWpos : W > 0 := (StandardEncoding Γ).W_pos
  -- Convert decode_symbol_inv → decode_bit_inv at x = 0
  have h_bit0 :
    decode_bit_inv change_of_alphabet input cfg (k := input.length) (by omega)
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
      StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfgW ∧
      decode_bit_inv change_of_alphabet input cfgW (k := input.length) (by omega)
        ⟨W, by linarith⟩ :=
  by
    -- Induction on natural x ≤ W
    have :
      ∀ x : ℕ, (hx : x ≤ W) →
        ∃ cfgx,
          StepsTo (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg cfgx ∧
          decode_bit_inv change_of_alphabet input cfgx (k := input.length) (by omega)
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
        -- Now show x < W so we can use decode_bit_within_symbol
        have hx_lt : x < W := Nat.lt_of_succ_le hx
        obtain ⟨cfg_next, h_step, h_next_inv⟩ :=
          decode_bit_within_symbol
            change_of_alphabet M input
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
  -- Step 2: detect EOF using detect_EOF
  ----------------------------------------------------------------
  -- Extract components from decode_bit_inv at W
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
    detect_EOF change_of_alphabet M cfgW acc
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

lemma generator_gets_to_rewind_state {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
: ∃ cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)),
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    cfg.state = GenState.rewind
    ∧ cfg.workIndex = input.length - 1
    ∧ (∀ i (h : i < input.length),
        cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length →
        cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 →
        cfg.work (i : ℤ) = (default : Γ'))
    ∧ cfg.output = input
    ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg := by
  set gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
  let initialCfg := (initConfig gen
    (bitstreamFromInput input))
  have h_base_inv : decode_symbol_inv change_of_alphabet input initialCfg (k := 0) (by omega) := by
    unfold decode_symbol_inv
    simp only [initConfig, bitstreamFromInput, List.get_eq_getElem, Bool.if_false_right, zero_mul,
      CharP.cast_eq_zero, not_lt_zero, Int.toNat_natCast, IsEmpty.forall_iff, implies_true,
      zero_le, or_true, forall_const, List.take_zero, and_self, and_true, true_and, initialCfg]
    unfold gen
    simp [generatorFromTM0]
  have h_read_k_inputs :
    ∀ i (hi : i ≤ input.length),
      ∃ cfg' : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)),
        decode_symbol_inv change_of_alphabet input cfg' hi
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
        decode_one_symbol change_of_alphabet M input h_no_default cfg_i h_lt hInv_i
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
  obtain ⟨cfg_final, h_properties_of_cfg_final⟩ :=
    decode_EOF_marker change_of_alphabet M input cfg_all_decoded h_inv_all_decoded
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

lemma rewinding_goes_back_one {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ default ∉ input)
: step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg = some {
    state := GenState.rewind,
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := cfg.work,
    workIndex := cfg.workIndex - 1,
    output := cfg.output
} := by
  obtain ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩ := h
  unfold step generatorFromTM0
  simp only [h_state]
  -- Show that cfg.work (cfg.workIndex) ≠ default
  have h_not_blank : cfg.work cfg.workIndex ≠ default := by
    have h_eq : cfg.work cfg.workIndex =
        change_of_alphabet (input.get ⟨cfg.workIndex.toNat, by omega⟩) := by
      have := h_work_input cfg.workIndex.toNat (by omega)
      convert this using 2
      simp only [Int.ofNat_toNat, left_eq_sup]
      exact h_idx_nonneg
    rw [h_eq]
    intro h_contra
    apply h_no_blank
    have := hchange_injective (h_contra.trans hchange_default.symm)
    rw [← this]
    exact List.get_mem input ⟨cfg.workIndex.toNat, by omega⟩
  simp only [if_neg h_not_blank]
  norm_num
  constructor
  · funext x
    split_ifs with hx
    · rw [hx]
    · rfl
  · ring

lemma full_rewinding_gets_back_to_negative_index {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex < input.length
    ∧ cfg.workIndex ≥ 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    cfg'.state = GenState.rewind
    ∧ cfg'.workIndex = -1
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ'))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
  obtain ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_work_ge,
          h_work_neg, h_output, h_no_blank⟩ := h
  match n : cfg.workIndex.toNat with
  | 0 =>
    have h_idx_eq : cfg.workIndex = 0 := by omega
    let cfg' : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)) := {
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
      · exact rewinding_goes_back_one change_of_alphabet hchange_default hchange_injective
          M input cfg ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩
      · exact Steps.refl cfg'
  | m + 1 =>
    have h_idx_eq : cfg.workIndex = m + 1 := by omega
    let cfg_next : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)) := {
      state := GenState.rewind,
      input := cfg.input,
      inputIndex := cfg.inputIndex,
      work := cfg.work,
      workIndex := cfg.workIndex - 1,
      output := cfg.output
    }
    have h_step : step gen cfg = some cfg_next :=
      rewinding_goes_back_one change_of_alphabet hchange_default hchange_injective
        M input cfg ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input, h_no_blank⟩
    have h_ih_input : cfg_next.state = GenState.rewind
       ∧ cfg_next.workIndex < input.length
       ∧ cfg_next.workIndex ≥ 0
       ∧ (∀ i (h : i < input.length), cfg_next.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
       ∧ (∀ i : ℕ, i ≥ input.length → cfg_next.work (i : ℤ) = (default : Γ'))
       ∧ (∀ i : ℤ, i < 0 → cfg_next.work (i : ℤ) = (default : Γ'))
       ∧ cfg_next.output = input
       ∧ default ∉ input := by
         simp only [Order.sub_one_lt_iff, Int.sub_nonneg,
           List.get_eq_getElem, ge_iff_le, true_and, cfg_next]
         refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨cfg', h_final⟩ := full_rewinding_gets_back_to_negative_index
      change_of_alphabet hchange_default hchange_injective M input cfg_next h_ih_input
    use cfg'
    refine ⟨h_final.1, h_final.2.1, h_final.2.2.1, h_final.2.2.2.1,
      h_final.2.2.2.2.1, h_final.2.2.2.2.2.1, ?_⟩
    obtain ⟨k, h_steps⟩ := h_final.2.2.2.2.2.2
    use k + 1
    exact Steps.step cfg cfg_next cfg' k h_step h_steps
termination_by cfg.workIndex.toNat

lemma rewind_at_negative_index_leads_to_simulation {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = -1
    ∧ cfg.work (-1) = (default : Γ'))
: step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg = some {
    state := GenState.sim (default : Λ),
    input := cfg.input,
    inputIndex := cfg.inputIndex,
    work := cfg.work,
    workIndex := 0,
    output := cfg.output
} := by
  obtain ⟨h_state, h_idx, h_blank⟩ := h
  unfold step generatorFromTM0
  simp only [h_state, h_idx, h_blank, if_true]
  norm_num
  funext x
  split_ifs with hx
  · rw [hx, h_blank]
  · rfl

lemma rewinding_leads_to_simulation_readiness {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h : cfg.state = GenState.rewind
    ∧ cfg.workIndex = input.length - 1
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
    ∧ cfg.output = input
    ∧ default ∉ input)
: ∃ cfg',
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    cfg'.state = GenState.sim (default : Λ)
    ∧ cfg'.workIndex = 0
    ∧ (∀ i (h : i < input.length), cfg'.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length → cfg'.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg'.work (i : ℤ) = (default : Γ'))
    ∧ cfg'.output = input
    ∧ StepsTo gen cfg cfg' := by
  let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low, h_output, h_no_default⟩
    := h
  by_cases h_empty : input.length = 0
  · have h_idx_neg : cfg.workIndex = -1 := by simp [h_idx, h_empty]
    have h_work_neg : cfg.work (-1) = (default : Γ') := by
      apply h_work_blank_low
      norm_num
    have h_step := rewind_at_negative_index_leads_to_simulation change_of_alphabet M cfg
      ⟨h_state, h_idx_neg, h_work_neg⟩
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
  · have h_length_pos : input.length > 0 := by omega
    have h_idx_nonneg : cfg.workIndex ≥ 0 := by rw [h_idx]; omega
    have h_idx_bound : cfg.workIndex < input.length := by rw [h_idx]; omega
    have h_many_conditions : cfg.state = GenState.rewind
      ∧ cfg.workIndex < input.length
      ∧ cfg.workIndex ≥ 0
      ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
      ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ'))
      ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
      ∧ cfg.output = input
      ∧ default ∉ input :=
        ⟨h_state, h_idx_bound, h_idx_nonneg, h_work_input,
         h_work_blank_high, h_work_blank_low, h_output, h_no_default⟩
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output,
            h_steps_to_rewind⟩ :=
      full_rewinding_gets_back_to_negative_index change_of_alphabet hchange_default
        hchange_injective M input cfg h_many_conditions
    have h_rewind_work_neg : rewindCfg.work (-1) = (default : Γ') :=
      h_rewind_work_blank_low (-1) (by omega)
    have h_step := rewind_at_negative_index_leads_to_simulation change_of_alphabet M rewindCfg
      ⟨h_rewind_state, h_rewind_idx, h_rewind_work_neg⟩
    let finalCfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)) := {
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

lemma generator_gets_to_simulation_state {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (h_no_default : default ∉ input)
: ∃ cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)),
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < input.length),
        cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length →
        cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 →
        cfg.work (i : ℤ) = (default : Γ'))
    ∧ cfg.output = input
    ∧ StepsTo gen (initConfig gen (bitstreamFromInput input)) cfg := by
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    obtain ⟨rewindCfg, h_rewind_state, h_rewind_idx, h_rewind_work_input,
            h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_init_to_rewind⟩ :=
      generator_gets_to_rewind_state change_of_alphabet M input h_no_default
    have h_rewind_conditions : rewindCfg.state = GenState.rewind
      ∧ rewindCfg.workIndex = input.length - 1
      ∧ (∀ i (h : i < input.length), rewindCfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
      ∧ (∀ i : ℕ, i ≥ input.length → rewindCfg.work (i : ℤ) = (default : Γ'))
      ∧ (∀ i : ℤ, i < 0 → rewindCfg.work (i : ℤ) = (default : Γ'))
      ∧ rewindCfg.output = input
      ∧ default ∉ input :=
        ⟨h_rewind_state, h_rewind_idx, h_rewind_work_input,
         h_rewind_work_blank_high, h_rewind_work_blank_low, h_rewind_output, h_no_default⟩
    obtain ⟨simCfg, h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
            h_sim_work_blank_low, h_sim_output, h_rewind_to_sim⟩ :=
      rewinding_leads_to_simulation_readiness change_of_alphabet hchange_default hchange_injective
        M input rewindCfg h_rewind_conditions
    use simCfg
    refine ⟨h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
            h_sim_work_blank_low, h_sim_output, ?_⟩
    obtain ⟨n1, steps1⟩ := h_init_to_rewind
    obtain ⟨n2, steps2⟩ := h_rewind_to_sim
    use n1 + n2
    exact Steps.trans steps1 steps2

structure ConfigurationsMatch {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (genCfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ' Λ) : Prop where
  states_match : genCfg.state =
    GenState.sim (Λ := Λ) (Γ := Γ) (enc_Γ := StandardEncoding Γ) tm0Cfg.q
  heads_match : genCfg.work genCfg.workIndex = tm0Cfg.Tape.head
  tape_match_right : ∀ (d : ℕ), genCfg.work (genCfg.workIndex + 1 + d) =
    Turing.ListBlank.nth tm0Cfg.Tape.right d
  tape_match_left : ∀ (d : ℕ), genCfg.work (genCfg.workIndex - 1 - d) =
    Turing.ListBlank.nth tm0Cfg.Tape.left d

def maybe_configurations_match {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (maybeGenCfg : Option (GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ))))
  (maybeTm0Cfg : Option (Turing.TM0.Cfg Γ' Λ)) : Prop :=
match maybeGenCfg, maybeTm0Cfg with
| none, none => True
| some genCfg, some tm0Cfg => ConfigurationsMatch genCfg tm0Cfg
| _, _ => False

lemma matching_configurations_step_simultaneously {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine Γ' Λ)
  (genCfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ' Λ)
  (h_match : ConfigurationsMatch genCfg tm0Cfg)
  : maybe_configurations_match
      (step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) genCfg)
      (Turing.TM0.step M tm0Cfg) := by
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
  unfold step generatorFromTM0 Turing.TM0.step maybe_configurations_match
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
        have h_next_gen : step (generatorFromTM0 change_of_alphabet M) genCfg = some {
          state := GenState.sim q'
          input := genCfg.input
          inputIndex := genCfg.inputIndex
          work := genCfg.work
          workIndex := genCfg.workIndex - 1
          output := genCfg.output
        } := by
          unfold step generatorFromTM0
          simp only [h_state]
          simp only [h_head]
          simp only [h_M, add_zero, Int.reduceNeg, Option.some.injEq,
            GenConfig.mk.injEq, and_true, true_and]
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
        have h_next_gen : step (generatorFromTM0 change_of_alphabet M) genCfg = some {
          state := GenState.sim q'
          input := genCfg.input
          inputIndex := genCfg.inputIndex
          work := genCfg.work
          workIndex := genCfg.workIndex + 1
          output := genCfg.output
        } := by
          unfold step generatorFromTM0
          simp only [h_state]
          simp only [h_head]
          simp only [h_M, add_zero, Option.some.injEq,
            GenConfig.mk.injEq, and_true, true_and]
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

lemma simStaysInSimAndPreservesOutput {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (cfg cfg' : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_state : ∃ q, cfg.state = GenState.sim q)
  (h_step : step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    cfg = some cfg') :
  cfg'.output = cfg.output ∧ (∃ q', cfg'.state = GenState.sim q') := by
  obtain ⟨q, hq⟩ := h_state
  unfold step generatorFromTM0 at h_step
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

lemma simulationWorksOnceWeAreReady {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (input : List Γ)
  (h_halts : (Turing.TM0.eval M (input.map change_of_alphabet)).Dom)
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_cfg :
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < input.length), cfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ input.length → cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
    ∧ cfg.output = input
    ∧ default ∉ input
  ) :
  ∃ haltCfg,
    let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
    StepsTo gen cfg haltCfg
    ∧ haltingConfig gen haltCfg
    ∧ haltCfg.output = input := by
  --
  obtain ⟨h_state, h_idx, h_work_input, h_work_blank_high, h_work_blank_low,
    h_output, h_no_default⟩ := h_cfg
  --
  -- Step 1: Show `cfg` matches the TM0 initial configuration
  have h_match_init : ConfigurationsMatch cfg (Turing.TM0.init (input.map change_of_alphabet)) := by
    constructor
    · exact h_state
    · rw [h_idx]
      unfold Turing.TM0.init Turing.Tape.mk₁
      cases h : input with
      | nil =>
        simp only [List.map_nil, Turing.Tape.mk₂, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_nil]
        have : input.length = 0 := by simp [h]
        exact h_work_blank_high 0 (by omega)
      | cons head tail =>
        simp only [List.map_cons, Turing.Tape.mk₂, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_cons]
        have h0 : 0 < input.length := by simp [h]
        have := h_work_input 0 h0
        simp only [Int.ofNat_zero] at this
        rw [this]
        congr 1
        simp [h]
    · intro d
      unfold Turing.TM0.init Turing.Tape.mk₁
      rw [h_idx]
      simp only [Turing.ListBlank.nth]
      cases h : input with
      | nil =>
        simp only [List.map_nil, zero_add, Turing.Tape.mk₂, Turing.Tape.mk'_right,
          Turing.ListBlank.tail_mk, List.tail_nil]
        exact h_work_blank_high (1 + d) (by simp [h])
      | cons head tail =>
        simp only [List.map_cons, zero_add, Turing.Tape.mk₂, Turing.ListBlank.mk,
            Turing.Tape.mk'_right, Turing.ListBlank.tail, Quotient.mk'']
        simp only [List.getI, List.getD_eq_getElem?_getD]
        by_cases hd : d < tail.length
        · have hget : (tail.map change_of_alphabet)[d]? =
              some (change_of_alphabet (tail[d])) := by
            rw [List.getElem?_map, List.getElem?_eq_getElem hd]
            simp
          simp only [Quotient.liftOn'_mk'', List.tail_cons, hget, Option.getD_some]
          have htail : tail[d] = input.get ⟨d + 1, by simp [h]; omega⟩ := by simp [h]
          rw [htail]
          convert h_work_input (1 + d) (by simp [h]; omega) using 2
          ring_nf
        · simp only [Quotient.liftOn'_mk'', List.tail_cons]
          have : (tail.map change_of_alphabet)[d]? = none := by
            rw [List.getElem?_eq_none]
            simp only [List.length_map]
            omega
          simp only [this, Option.getD_none]
          exact h_work_blank_high (1 + d) (by simp [h]; omega)
    · intro d
      unfold Turing.TM0.init Turing.Tape.mk₁
      rw [h_idx]
      simp only [zero_sub, Int.reduceNeg, Turing.ListBlank.nth, Turing.Tape.mk₂,
        Turing.Tape.mk'_left]
      exact h_work_blank_low _ (by omega)
  --
  -- Step 2: Use halting assumption to get a halting TM0 configuration
  obtain ⟨tmCfg, h_reaches, h_tm_halt⟩ : ∃ tmCfg,
      Turing.TM0.Reaches M (Turing.TM0.init (input.map change_of_alphabet)) tmCfg
      ∧ Turing.TM0.step M tmCfg = none := by
    unfold Turing.TM0.eval at h_halts
    obtain ⟨output, h_out⟩ := Part.dom_iff_mem.mp h_halts
    rw [Part.mem_map_iff] at h_out
    obtain ⟨cfg, h_cfg, _⟩ := h_out
    rw [Turing.mem_eval] at h_cfg
    obtain ⟨h_reaches, h_halt⟩ := h_cfg
    exact ⟨cfg, h_reaches, h_halt⟩
  --
  -- Step 3: Induction over `Reaches` to propagate `ConfigurationsMatch` through steps
  have h_sim :
    ∀ {tmCfg cfg},
      Turing.TM0.Reaches M (Turing.TM0.init (input.map change_of_alphabet)) tmCfg →
      ConfigurationsMatch cfg (Turing.TM0.init (input.map change_of_alphabet)) →
      (∃ q, cfg.state = GenState.sim q) →
      cfg.output = input →
      ∃ genCfg,
        let gen := generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M
        StepsTo gen cfg genCfg ∧ ConfigurationsMatch genCfg tmCfg
          ∧ (∃ q, genCfg.state = GenState.sim q) ∧ genCfg.output = input := by
    intro tmCfg cfg h_reaches h_match h_sim_state h_out
    induction h_reaches with
    | refl =>
      exact ⟨cfg, ⟨0, Steps.refl cfg⟩, h_match, h_sim_state, h_out⟩
    | @tail b c prev one_step IH =>
      obtain ⟨genCfg₁, h_ih_properties⟩ := IH
      dsimp at h_ih_properties
      obtain ⟨h_steps₁, h_match₁, h_sim_state₁, h_out₁⟩ := h_ih_properties
      have h_sim_step := matching_configurations_step_simultaneously
        change_of_alphabet M genCfg₁ b h_match₁
      unfold maybe_configurations_match at h_sim_step
      rw [one_step] at h_sim_step
      cases h_gen_step : step
          (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) genCfg₁ with
      | none =>
        rw [h_gen_step] at h_sim_step
        contradiction
      | some genCfg₂ =>
        rw [h_gen_step] at h_sim_step
        use genCfg₂
        constructor
        · obtain ⟨n, h_n⟩ := h_steps₁
          use n + 1
          have one_step_gen : Steps
              (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
              genCfg₁ genCfg₂ 1 :=
            Steps.step genCfg₁ genCfg₂ genCfg₂ 0 h_gen_step (Steps.refl genCfg₂)
          exact Steps.trans h_n one_step_gen
        constructor
        · exact h_sim_step
        · have ⟨h_preserve_out, h_stay_sim⟩ :=
            simStaysInSimAndPreservesOutput change_of_alphabet M genCfg₁ genCfg₂
              h_sim_state₁ h_gen_step
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
      (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) haltCfg := by
    unfold haltingConfig
    have h_sim_halt := matching_configurations_step_simultaneously
      change_of_alphabet M haltCfg tmCfg h_match
    unfold maybe_configurations_match at h_sim_halt
    rw [h_tm_halt] at h_sim_halt
    cases h_gen : step
        (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) haltCfg with
    | none => rfl
    | some _ =>
      rw [h_gen] at h_sim_halt
      contradiction
  --
  refine ⟨h_steps, h_haltCfg_halts, h_output_input⟩

lemma generatorFromTM0_supports {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S) :
  ∃ (S' : Finset (GenState Λ Γ (StandardEncoding Γ))),
    GeneratorSupports (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) S' := by
  let S'_set : Set (GenState Λ Γ (StandardEncoding Γ)) :=
    (Set.range GenState.load)
    ∪ {GenState.rewind}
    ∪ (GenState.sim '' ↑S)
  -- Argue it is finite
  have hfin : S'_set.Finite := by
    apply Set.Finite.union
    · apply Set.Finite.union
      · exact Set.finite_range GenState.load
      · exact Set.finite_singleton _
    · exact Set.Finite.image _ S.finite_toSet
  -- Convert to Finset
  refine ⟨hfin.toFinset, ?_⟩
  constructor
  · rw [Set.Finite.mem_toFinset]
    simp [S'_set, generatorFromTM0]
  · intro q hq b w q' w' o itd wtd h_δ
    rw [Set.Finite.mem_toFinset]
    rw [Set.Finite.mem_toFinset] at hq
    -- Case split on which part of S'_set q comes from
    simp only [S'_set, Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_image,
               Finset.mem_coe]
    simp only [generatorFromTM0] at h_δ
    cases q with
    | load ls =>
      simp only at h_δ
      split at h_δ
      · split at h_δ
        · -- enc_Γ.enum = none → rewind
          simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
          left; right; rfl
        · rename_i g
          split at h_δ
          · -- g = default → rewind
            simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
            left; right; rfl
          · -- g ≠ default → load
            simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
            left; left; exact ⟨_, rfl⟩
      · -- still reading → load
        simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
        left; left; exact ⟨_, rfl⟩
    | rewind =>
      simp only at h_δ
      split at h_δ
      · -- w = default → sim default
        simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
        right; exact ⟨default, hS.1, rfl⟩
      · -- not rewound → rewind
        simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
        left; right; rfl
    | sim q_tm =>
      -- Extract q_tm ∈ S from hq
      have hq_tm : q_tm ∈ S := by
        rcases hq with ((⟨ls, h⟩ | h) | ⟨q'', hq'', h⟩)
        · simp at h
        · simp at h
        · have : q'' = q_tm := GenState.sim.inj h
          exact this ▸ hq''
      simp only at h_δ
      split at h_δ
      · contradiction
      · rename_i q'_tm stmt hM
        have hq'_tm : q'_tm ∈ S := hS.2 (q := q_tm) (by exact_mod_cast hM) (by exact_mod_cast hq_tm)
        cases stmt with
        | move dir =>
          cases dir with
          | left  =>
            simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
            right; exact ⟨q'_tm, hq'_tm, rfl⟩
          | right =>
            simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
            right; exact ⟨q'_tm, hq'_tm, rfl⟩
        | write g =>
          simp only [Option.some.injEq] at h_δ; obtain ⟨rfl, -⟩ := h_δ
          right; exact ⟨q'_tm, hq'_tm, rfl⟩

theorem anything_a_tm0_recognises_can_be_generated_by_its_generator {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S)
  (input : List Γ)
  (h_no_default : default ∉ input)
  (h_halts : (Turing.TM0.eval M (input.map change_of_alphabet)).Dom) :
  input ∈ (generatedLanguage
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (generatorFromTM0_supports change_of_alphabet M S hS).choose
    (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).val := by
    let enc_Γ := StandardEncoding Γ
    let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
    rcases generator_gets_to_simulation_state change_of_alphabet hchange_default hchange_injective
      M input h_no_default
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
    have h_ready : readyCfg.state = GenState.sim (default : Λ)
      ∧ readyCfg.workIndex = 0
      ∧ (∀ i (h : i < input.length), readyCfg.work (i : ℤ) = change_of_alphabet (input.get ⟨i, h⟩))
      ∧ (∀ i : ℕ, i ≥ input.length → readyCfg.work (i : ℤ) = (default : Γ'))
      ∧ (∀ i : ℤ, i < 0 → readyCfg.work i = (default : Γ'))
      ∧ readyCfg.output = input
      ∧ default ∉ input :=
        ⟨h_readyCfg_initial_state, h_readyCfg_work_index_zero,
         h_readyCfg_work_tape_contains_input, h_readyCfg_work_tape_blank_above,
         h_readyCfg_work_tape_blank_below, h_readyCfg_output_is_input, h_no_default⟩
    rcases simulationWorksOnceWeAreReady change_of_alphabet M input h_halts readyCfg h_ready
      with ⟨haltCfg, h_steps_to_halt, h_is_halting, h_halt_output⟩
    have h_whole_run : StepsTo gen (initConfig gen (bitstreamFromInput input)) haltCfg := by
      obtain ⟨n1, h1⟩ := h_initial_stepsTo_readyCfg
      obtain ⟨n2, h2⟩ := h_steps_to_halt
      use n1 + n2
      exact Steps.trans h1 h2
    have h_computes : Computes gen (initConfig gen (bitstreamFromInput input)) haltCfg.output :=
      StepsTo.computes h_whole_run h_is_halting
    rw [h_halt_output] at h_computes
    use bitstreamFromInput input

def loading_inv {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ))) : Prop :=
  (∃ ls, cfg.state = GenState.load ls)
  ∧ cfg.workIndex = cfg.output.length
  ∧ (∀ i (h : i < cfg.output.length),
      cfg.work (i : ℤ) = change_of_alphabet (cfg.output.get ⟨i, h⟩))
  ∧ (∀ i : ℕ, i ≥ cfg.output.length → cfg.work (i : ℤ) = (default : Γ'))
  ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
  ∧ default ∉ cfg.output

def rewinding_config {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ))) : Prop :=
  cfg.state = GenState.rewind
  ∧ cfg.workIndex = cfg.output.length - 1
  ∧ (∀ i (h : i < cfg.output.length),
      cfg.work (i : ℤ) = change_of_alphabet (cfg.output.get ⟨i, h⟩))
  ∧ (∀ i : ℕ, i ≥ cfg.output.length → cfg.work (i : ℤ) = (default : Γ'))
  ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
  ∧ default ∉ cfg.output

lemma loading_inv_preserved_or_becomes_rewinding {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (cfg cfg' : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (h_inv : loading_inv change_of_alphabet cfg)
  (h_step : step (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg =
    some cfg')
  : loading_inv change_of_alphabet cfg' ∨ rewinding_config change_of_alphabet cfg' := by
  obtain ⟨⟨ls, h_state⟩, h_idx, h_work_output, h_work_high, h_work_low, h_no_default⟩ := h_inv
  --
  unfold step generatorFromTM0 at h_step
  simp only [h_state] at h_step
  --
  -- Now split on whether we're done reading bits for this symbol
  by_cases h_done : ls.bitsRead.val = (StandardEncoding Γ).W
  · -- Case: bitsRead.val = W (done reading a symbol)
    simp only [h_done, ↓reduceDIte] at h_step
    -- Now split on what enum returns
    cases h_enum : (StandardEncoding Γ).enum ls.acc with
    | none =>
      -- Case: enum returns none (EOF detected)
      simp only [h_enum] at h_step
      -- Extract cfg' from the equation
      injection h_step with h_cfg'
      right
      unfold rewinding_config
      rw [← h_cfg']
      simp only [h_idx]
      constructor
      · -- cfg'.state = GenState.rewind
        trivial
      constructor
      · -- cfg'.workIndex = cfg'.output.length - 1
        ring
      constructor
      · -- ∀ i (h : i < cfg'.output.length), cfg'.work ↑i = cfg'.output.get ⟨i, h⟩
        intro i hi
        split_ifs with heq
        · -- i = cfg.workIndex
          simp only at heq
          omega
        · -- i ≠ cfg.workIndex
          exact h_work_output i hi
      constructor
      · -- ∀ i : ℕ, i ≥ cfg'.output.length → cfg'.work ↑i = default
        intro i hi
        split_ifs with heq
        · -- i = cfg.workIndex
          apply h_work_high
          simp only at heq
          omega
        · -- i ≠ cfg.workIndex
          exact h_work_high i hi
      constructor
      · -- ∀ i : ℤ, i < 0 → cfg'.work i = default
        intro i hi
        split_ifs with heq
        · -- i = cfg.workIndex
          subst heq
          omega
        · -- i ≠ cfg.workIndex
          exact h_work_low i hi
      · -- default ∉ cfg'.output
        exact h_no_default
    | some g =>
      -- Case: enum returns some g
      simp only [h_enum] at h_step
      -- Now split on whether g = default
      by_cases h_g_default : g = default
      · -- Case: g = default (transition to rewind)
        simp only [h_g_default, ↓reduceIte] at h_step
        injection h_step with h_cfg'
        right
        unfold rewinding_config
        rw [← h_cfg']
        simp only [h_idx]
        constructor
        · -- cfg'.state = GenState.rewind
          trivial
        constructor
        · -- cfg'.workIndex = cfg'.output.length - 1
          ring
        constructor
        · -- ∀ i (h : i < cfg'.output.length), cfg'.work ↑i = cfg'.output.get ⟨i, h⟩
          intro i hi
          split_ifs with heq
          · -- i = cfg.workIndex
            simp only at heq
            omega
          · -- i ≠ cfg.workIndex
            exact h_work_output i hi
        constructor
        · -- ∀ i : ℕ, i ≥ cfg'.output.length → cfg'.work ↑i = default
          intro i hi
          split_ifs with heq
          · -- i = cfg.workIndex
            apply h_work_high
            simp only at heq
            omega
          · -- i ≠ cfg.workIndex
            exact h_work_high i hi
        constructor
        · -- ∀ i : ℤ, i < 0 → cfg'.work i = default
          intro i hi
          split_ifs with heq
          · -- i = cfg.workIndex
            subst heq
            omega
          · -- i ≠ cfg.workIndex
            exact h_work_low i hi
        · -- default ∉ cfg'.output
          exact h_no_default
      · -- Case: g ≠ default (write symbol and continue loading)
        simp only [h_g_default, ↓reduceIte] at h_step
        injection h_step with h_cfg'
        left
        unfold loading_inv
        rw [← h_cfg']
        simp only [h_idx]
        constructor
        · -- ∃ ls, cfg'.state = GenState.load ls
          use { bitsRead := 0, acc := 0, accBound := by simp }
        constructor
        · -- cfg'.workIndex = cfg'.output.length
          simp only [List.length_append, List.length_singleton]
          omega
        constructor
        · -- ∀ i (h : i < cfg'.output.length), cfg'.work ↑i = cfg'.output.get ⟨i, h⟩
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          split_ifs with heq
          · -- i = cfg.workIndex
            simp only at heq
            simp only [List.get_eq_getElem]
            have : i = cfg.output.length := by omega
            subst this
            simp
          · -- i ≠ cfg.workIndex
            by_cases h : i < cfg.output.length
            · have hi_append : i < (cfg.output ++ [g]).length := by
                simp
                omega
              have : (cfg.output ++ [g]).get ⟨i, hi_append⟩ = cfg.output.get ⟨i, h⟩ := by
                simp only [List.get_eq_getElem]
                rw [List.getElem_append_left h]
              rw [this]
              exact h_work_output i h
            · have : i = cfg.output.length := by
                linarith
              subst this
              simp only [List.get_eq_getElem]
              rw [List.getElem_append_right (by omega)]
              simp only [tsub_self, List.getElem_cons_zero]
              exfalso
              apply heq
              rfl
        constructor
        · -- ∀ i : ℕ, i ≥ cfg'.output.length → cfg'.work ↑i = default
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          split_ifs with heq
          · -- i = cfg.workIndex
            simp only at heq
            omega
          · -- i ≠ cfg.workIndex
            exact h_work_high i (by omega)
        constructor
        · -- ∀ i : ℤ, i < 0 → cfg'.work i = default
          intro i hi
          split_ifs with heq
          · -- i = cfg.workIndex
            subst heq
            omega
          · -- i ≠ cfg.workIndex
            exact h_work_low i hi
        · -- default ∉ cfg'.output
          intro h_contra
          simp only [List.mem_append, List.mem_singleton] at h_contra
          cases h_contra with
          | inl h_in_old => trivial
          | inr h_eq => exact h_g_default h_eq.symm
  · -- Case: bitsRead.val ≠ W (still reading bits)
    simp only [h_done, ↓reduceDIte] at h_step
    injection h_step with h_cfg'
    left
    unfold loading_inv
    rw [← h_cfg']
    simp only [h_idx]
    constructor
    · -- ∃ ls, cfg'.state = GenState.load ls
      use { bitsRead := ⟨↑ls.bitsRead + 1, by omega⟩,
            acc := ⟨2 * ↑ls.acc + if cfg.input cfg.inputIndex = true then 1 else 0, by
            have h_bitsRead_lt_W : ls.bitsRead.val < (StandardEncoding Γ).W := by omega
            have h_acc_bound : ls.acc.val ≤ 2 ^ ls.bitsRead.val - 1 := ls.accBound
            have h_bit : (if cfg.input cfg.inputIndex = true then 1 else 0) ≤ 1 :=
              by split_ifs <;> omega
            have h_pow_le : 2 ^ (ls.bitsRead.val + 1) ≤ 2 ^ (StandardEncoding Γ).W :=
              Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h_bitsRead_lt_W)
            calc 2 * ls.acc.val + (if cfg.input cfg.inputIndex = true then 1 else 0)
                ≤ 2 * (2 ^ ls.bitsRead.val - 1) + 1 := by omega
              _ = 2 * 2 ^ ls.bitsRead.val - 1 := by
                  have h_pos : 1 ≤ 2 ^ ls.bitsRead.val := Nat.one_le_pow _ _ (by norm_num)
                  rw [Nat.mul_sub_left_distrib]
                  omega
              _ = 2 ^ (ls.bitsRead.val + 1) - 1 := by rw [pow_succ]; ring_nf
              _ < 2 ^ (ls.bitsRead.val + 1) := by
                apply Nat.sub_lt
                · apply Nat.pos_of_ne_zero
                  norm_num
                · norm_num
              _ ≤ 2 ^ (StandardEncoding Γ).W := h_pow_le
            ⟩,
            accBound := by
              simp only
              have h_acc_bound : ls.acc.val ≤ 2 ^ ls.bitsRead.val - 1 := ls.accBound
              have h_bit : (if cfg.input cfg.inputIndex = true then 1 else 0) ≤ 1 :=
                by split_ifs <;> omega
              calc 2 * ls.acc.val + (if cfg.input cfg.inputIndex = true then 1 else 0)
                  ≤ 2 * (2 ^ ls.bitsRead.val - 1) + 1 := by omega
                _ = 2 * 2 ^ ls.bitsRead.val - 1 := by
                  have h_pos : 1 ≤ 2 ^ ls.bitsRead.val := Nat.one_le_pow _ _ (by norm_num)
                  rw [Nat.mul_sub_left_distrib]
                  omega
                _ = 2 ^ (ls.bitsRead.val + 1) - 1 := by rw [pow_succ]; ring_nf
            }
    constructor
    · -- cfg'.workIndex = cfg'.output.length
      ring
    constructor
    · -- ∀ i (h : i < cfg'.output.length), cfg'.work ↑i = cfg'.output.get ⟨i, h⟩
      intro i hi
      split_ifs with heq
      · have : i = cfg.output.length := by omega
        subst this
        omega
      · exact h_work_output i hi
    constructor
    · -- ∀ i : ℕ, i ≥ cfg'.output.length → cfg'.work ↑i = default
      intro i hi
      split_ifs with heq
      · have : i = cfg.output.length := by omega
        subst this
        exact h_work_high cfg.output.length (by omega)
      · exact h_work_high i hi
    constructor
    · -- ∀ i : ℤ, i < 0 → cfg'.work i = default
      intro i hi
      split_ifs with heq
      · subst heq
        omega
      · exact h_work_low i hi
    · -- default ∉ cfg'.output
      exact h_no_default

lemma generation_must_get_ready_to_rewind {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (bitstream : ℕ → Bool)
  (output : List Γ)
  (h_computes : Computes
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (initConfig (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) bitstream)
    output)
:
  let enc_Γ := StandardEncoding Γ
  let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
  ∃ cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)),
    rewinding_config change_of_alphabet cfg
    ∧ StepsTo gen (initConfig gen bitstream) cfg
    ∧ default ∉ cfg.output
:= by
  let enc_Γ := StandardEncoding Γ
  let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
  -- First, show that the initial configuration satisfies loading_inv
  have h_init_loading : loading_inv change_of_alphabet (initConfig gen bitstream) := by
    unfold loading_inv initConfig
    simp only [List.get_eq_getElem, CharP.cast_eq_zero,
      List.not_mem_nil, true_and]
    constructor
    · use { bitsRead := 0, acc := 0, accBound := by simp }
      rfl
    constructor
    · intro i hi
      simp at hi
    constructor
    · intro i hi
      rfl
    constructor
    · intro i _
      rfl
    · simp
  -- Key lemma: a loading state is never a halting configuration
  have load_not_halting : ∀ cfg, loading_inv change_of_alphabet cfg → ¬haltingConfig gen cfg := by
    intro cfg h_load h_halt
    unfold haltingConfig at h_halt
    unfold step at h_halt
    obtain ⟨⟨ls, h_state⟩, _⟩ := h_load
    simp only [h_state] at h_halt
    -- In the load state, we always split on whether bitsRead = W
    -- In both branches, we get some (not none)
    split at h_halt
    · -- bitsRead = W case
      rename_i heq
      show False
      have : gen = generatorFromTM0 change_of_alphabet M := rfl
      rw [this] at heq
      unfold generatorFromTM0 at heq
      simp at heq
      split at heq
      · split at heq
        · simp at heq
        · split at heq <;> simp at heq
      · simp at heq
    · -- bitsRead ≠ W case
      simp at h_halt
  -- Since Computes holds and we start in loading_inv,
  -- we must eventually reach rewinding_config
  -- (because we can't halt in loading_inv and loading_inv either persists or becomes
  -- rewinding_config)
  have eventually_rewinding : ∃ cfg,
      StepsTo gen (initConfig gen bitstream) cfg ∧
      rewinding_config change_of_alphabet cfg ∧
      default ∉ cfg.output := by
    -- Generalize to arbitrary starting configuration
    suffices ∀ start_cfg, loading_inv change_of_alphabet start_cfg →
      Computes gen start_cfg output →
      ∃ cfg, StepsTo gen start_cfg cfg ∧ rewinding_config change_of_alphabet cfg
        ∧ default ∉ cfg.output
    by exact this (initConfig gen bitstream) h_init_loading h_computes
    intro start_cfg h_loading h_comp
    induction h_comp with
    | halt cfg h_halt =>
      exfalso
      exact load_not_halting cfg h_loading h_halt
    | step cfg cfg' out h_step h_comp' ih =>
      -- Apply loading_inv_preserved_or_becomes_rewinding
      have h_inv := loading_inv_preserved_or_becomes_rewinding change_of_alphabet
        M cfg cfg' h_loading h_step
      cases h_inv with
      | inl h_still_loading =>
        -- Still in loading_inv, continue with IH
        -- Apply IH to cfg' which still satisfies loading_inv
        obtain ⟨final_cfg, h_steps_from_cfg', h_rewind, h_no_default⟩ :=
          ih h_computes h_still_loading
        -- Combine the steps: cfg → cfg' → final_cfg
        use final_cfg
        constructor
        · -- StepsTo gen cfg final_cfg
          refine StepsTo.trans gen ?_ h_steps_from_cfg'
          use 1
          exact Steps.step cfg cfg' cfg' 0 h_step (Steps.refl cfg')
        constructor
        · exact h_rewind
        · exact h_no_default
      | inr h_rewinding =>
        -- We've reached rewinding_config at cfg', so we're done
        use cfg'
        constructor
        · -- StepsTo gen cfg cfg'
          use 1
          exact Steps.step cfg cfg' cfg' 0 h_step (Steps.refl cfg')
        constructor
        · exact h_rewinding
        · -- Extract default ∉ cfg'.output from rewinding_config
          obtain ⟨_, _, _, _, _, h_no_default⟩ := h_rewinding
          exact h_no_default
  obtain ⟨cfg, h_steps, h_rewind, h_no_default⟩ := eventually_rewinding
  exact ⟨cfg, h_rewind, h_steps, h_no_default⟩

-- Helper lemma: if we're in sim state and compute output, our current output equals the
-- final output
lemma sim_output_eq_final_output {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (output : List Γ)
  (h_sim : ∃ q, cfg.state = GenState.sim q)
  (h_comp : Computes (generatorFromTM0 (enc_Γ := StandardEncoding Γ)
    change_of_alphabet M) cfg output) :
  cfg.output = output := by
  induction h_comp with
  | halt cfg h_halt => rfl
  | step cfg cfg' out h_step h_comp' ih =>
    have ⟨h_preserve, h_sim'⟩ := simStaysInSimAndPreservesOutput
      change_of_alphabet M cfg cfg' h_sim h_step
    have : cfg'.output = out := ih h_sim'
    rw [← h_preserve]
    exact this

lemma generation_must_get_ready_to_simulate {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (bitstream : ℕ → Bool)
  (output : List Γ)
  (h_computes : Computes
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (initConfig (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) bitstream)
    output)
:
  let enc_Γ := StandardEncoding Γ
  let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
  ∃ cfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)),
    cfg.state = GenState.sim (default : Λ)
    ∧ cfg.workIndex = 0
    ∧ (∀ i (h : i < cfg.output.length),
        cfg.work (i : ℤ) = change_of_alphabet (cfg.output.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ cfg.output.length → cfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → cfg.work (i : ℤ) = (default : Γ'))
    ∧ default ∉ cfg.output
    ∧ StepsTo gen (initConfig gen bitstream) cfg
    ∧ Computes (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M) cfg output
    ∧ cfg.output = output
:= by
  let enc_Γ := StandardEncoding Γ
  let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
  -- First, get to the rewind state
  obtain ⟨rewindCfg, h_rewind_inv, h_steps_to_rewind, h_no_default_output⟩ :=
    generation_must_get_ready_to_rewind change_of_alphabet M bitstream output h_computes
  -- Extract the components of rewinding_config
  obtain ⟨h_rewind_state, h_rewind_idx, h_rewind_work_input,
          h_rewind_work_blank_high, h_rewind_work_blank_low, h_no_default⟩ := h_rewind_inv
  -- Build the hypothesis for rewinding_leads_to_simulation_readiness
  have h_rewind_conditions : rewindCfg.state = GenState.rewind
    ∧ rewindCfg.workIndex = rewindCfg.output.length - 1
    ∧ (∀ i (h : i < rewindCfg.output.length), rewindCfg.work (i : ℤ) =
      change_of_alphabet (rewindCfg.output.get ⟨i, h⟩))
    ∧ (∀ i : ℕ, i ≥ rewindCfg.output.length → rewindCfg.work (i : ℤ) = (default : Γ'))
    ∧ (∀ i : ℤ, i < 0 → rewindCfg.work (i : ℤ) = (default : Γ'))
    ∧ rewindCfg.output = rewindCfg.output
    ∧ default ∉ rewindCfg.output :=
      ⟨h_rewind_state, h_rewind_idx, h_rewind_work_input,
       h_rewind_work_blank_high, h_rewind_work_blank_low, rfl, h_no_default⟩
  -- Apply rewinding_leads_to_simulation_readiness
  obtain ⟨simCfg, h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
          h_sim_work_blank_low, h_sim_output, h_rewind_to_sim⟩ :=
    rewinding_leads_to_simulation_readiness change_of_alphabet hchange_default hchange_injective
      M rewindCfg.output rewindCfg h_rewind_conditions
  -- Combine the steps: initConfig → rewindCfg → simCfg
  have h_steps_to_sim : StepsTo gen (initConfig gen bitstream) simCfg :=
    StepsTo.trans gen h_steps_to_rewind h_rewind_to_sim
  -- Use Computes.of_StepsTo to get Computes gen simCfg output
  have h_computes_from_sim : Computes gen simCfg output :=
    Computes.of_StepsTo h_computes h_steps_to_sim
  -- Prove that simCfg.output = output using the helper lemma
  have h_output_eq : simCfg.output = output :=
    sim_output_eq_final_output change_of_alphabet M simCfg output
      ⟨default, h_sim_state⟩ h_computes_from_sim
  -- Establish that rewindCfg.output = output
  have h_rewind_output_eq : rewindCfg.output = output := by
    rw [← h_output_eq, h_sim_output]
  -- Return simCfg with all properties
  use simCfg
  refine ⟨h_sim_state, h_sim_idx, ?_, ?_, h_sim_work_blank_low, ?_, h_steps_to_sim,
    h_computes_from_sim, h_output_eq⟩
  · intro i hi
    have hi' : i < rewindCfg.output.length := by
      calc i < simCfg.output.length := hi
        _ = output.length := by rw [h_output_eq]
        _ = rewindCfg.output.length := by rw [← h_rewind_output_eq]
    have hget : simCfg.output.get ⟨i, hi⟩ = rewindCfg.output.get ⟨i, hi'⟩ := by
      simp [h_sim_output]
    rw [hget]
    exact h_sim_work_input i hi'
  · -- ∀ i : ℕ, i ≥ simCfg.output.length → simCfg.work ↑i = default
    intro i hi
    rw [h_output_eq] at hi
    rw [← h_rewind_output_eq] at hi
    exact h_sim_work_blank_high i hi
  · -- default ∉ simCfg.output
    rw [h_output_eq]
    rw [← h_rewind_output_eq]
    exact h_no_default

lemma sim_steps_imply_tm0_steps {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (genCfg : GenConfig Γ' Γ (GenState Λ Γ (StandardEncoding Γ)))
  (tm0Cfg : Turing.TM0.Cfg Γ' Λ)
  (output : List Γ)
  (h_match : ConfigurationsMatch genCfg tm0Cfg)
  (h_computes : Computes (generatorFromTM0 (enc_Γ := StandardEncoding Γ)
    change_of_alphabet M) genCfg output)
  (h_output : genCfg.output = output) :
  ∃ tm0HaltCfg,
    Turing.TM0.Reaches M tm0Cfg tm0HaltCfg
    ∧ Turing.TM0.step M tm0HaltCfg = none
:= by
  revert h_output tm0Cfg
  induction h_computes with
  | halt cfg h_halt =>
    intro tm0Cfg h_match h_output
    use tm0Cfg
    constructor
    · exact Relation.ReflTransGen.refl
    · unfold haltingConfig step at h_halt
      have h_sim := matching_configurations_step_simultaneously
        change_of_alphabet M cfg tm0Cfg h_match
      unfold maybe_configurations_match at h_sim
      cases h_tm0 : Turing.TM0.step M tm0Cfg
      · trivial
      · rw [h_tm0] at h_sim
        simp only [reduceCtorEq]
        have h_step_none : step (generatorFromTM0 (enc_Γ := StandardEncoding Γ)
          change_of_alphabet M) cfg = none := h_halt
        rw [h_step_none] at h_sim
        exact h_sim
  | step cfg cfg' out h_step h_computes' ih =>
    intro tm0Cfg h_match h_output
    have h_sim := matching_configurations_step_simultaneously
      change_of_alphabet M cfg tm0Cfg h_match
    unfold maybe_configurations_match at h_sim
    rw [h_step] at h_sim
    cases h_tm0_step : Turing.TM0.step M tm0Cfg with
    | none =>
      rw [h_tm0_step] at h_sim
      contradiction
    | some tm0Cfg' =>
      rw [h_tm0_step] at h_sim
      have h_output' : cfg'.output = out := by
        have h_q : cfg.state = GenState.sim tm0Cfg.q := h_match.states_match
        have h_sim_state : ∃ q, cfg.state = GenState.sim q := ⟨tm0Cfg.q, h_q⟩
        obtain ⟨h_preserve, _⟩ := simStaysInSimAndPreservesOutput change_of_alphabet M cfg cfg'
          h_sim_state h_step
        rw [h_preserve]
        exact h_output
      obtain ⟨tm0HaltCfg, h_reaches', h_halt⟩ := ih tm0Cfg' h_sim h_output'
      use tm0HaltCfg
      constructor
      · exact Relation.ReflTransGen.head h_tm0_step h_reaches'
      · exact h_halt

theorem anything_a_generator_generates_is_recognised_by_its_tm0 {Γ Γ' Λ : Type u}
  [Inhabited Λ] [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S)
  (output : List Γ)
  (h_generated : output ∈
    (generatedLanguage
      (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
      (generatorFromTM0_supports change_of_alphabet M S hS).choose
      (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).val) :
  (Turing.TM0.eval M (output.map change_of_alphabet)).Dom := by
  let enc_Γ := StandardEncoding Γ
  let gen := generatorFromTM0 (enc_Γ := enc_Γ) change_of_alphabet M
  obtain ⟨bitstream, h_computes⟩ := h_generated
  obtain ⟨cfg, h_sim_state, h_sim_idx, h_sim_work_input, h_sim_work_blank_high,
          h_sim_work_blank_low, h_no_default_cfg, h_steps_to_sim, h_computes_from_cfg,
          h_output_eq⟩ :=
    generation_must_get_ready_to_simulate change_of_alphabet hchange_default hchange_injective
      M bitstream output h_computes
  have h_match : ConfigurationsMatch cfg (Turing.TM0.init (output.map change_of_alphabet)) := by
    constructor
    · exact h_sim_state
    · rw [h_sim_idx]
      unfold Turing.TM0.init Turing.Tape.mk₁
      cases h : output with
      | nil =>
        simp only [List.map_nil, Turing.Tape.mk₂, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_nil]
        apply h_sim_work_blank_high
        rw [h_output_eq, h]; simp
      | cons head tail =>
        simp only [List.map_cons, Turing.Tape.mk₂, Turing.Tape.mk'_head,
          Turing.ListBlank.head_mk, List.headI_cons]
        have h0 : 0 < cfg.output.length := by rw [h_output_eq, h]; simp
        have hget : cfg.output.get ⟨0, h0⟩ = head := by
          simp only [List.get_eq_getElem, h_output_eq, h, List.getElem_cons_zero]
        rw [← hget]
        exact h_sim_work_input 0 h0
    · intro d
      rw [h_sim_idx]
      simp only [Turing.TM0.init, Turing.Tape.mk₁, zero_add]
      unfold Turing.Tape.mk₂ Turing.Tape.mk'
      simp only [Turing.ListBlank.nth]
      cases h : output with
      | nil =>
        simp only [List.map_nil, Turing.ListBlank.mk]
        apply h_sim_work_blank_high
        rw [h_output_eq, h]; simp
      | cons head tail =>
        simp only [List.map_cons, Turing.ListBlank.mk]
        simp only [List.getI, List.getD_eq_getElem?_getD]
        by_cases hd : d < tail.length
        · have hget : (tail.map change_of_alphabet)[d]? =
              some (change_of_alphabet tail[d]) := by
            rw [List.getElem?_map, List.getElem?_eq_getElem hd]; simp
          have hlen : 1 + d < cfg.output.length := by
            rw [h_output_eq, h]; simp; omega
          rw [Turing.ListBlank.tail]
          simp only [Quotient.liftOn'_mk'', List.tail_cons]
          have htail : tail[d] = output.get ⟨d + 1, by rw [h]; simp; omega⟩ := by
            simp [h]
          have hcfg : cfg.output.get ⟨1 + d, hlen⟩ = tail[d] := by
            simp only [h_output_eq, h, List.get_eq_getElem]
            conv_lhs => arg 2; rw [add_comm]
            rw [List.getElem_cons_succ]
          simp only [Turing.ListBlank.mk, Quotient.liftOn'_mk'']
          have : cfg.work (1 + ↑d) = change_of_alphabet tail[d] := by
            have := h_sim_work_input (1 + d) hlen
            simp only [Nat.cast_add, Nat.cast_one] at this
            rw [this, hcfg]
          rw [this, hget, Option.getD_some]
        · have hnil : (tail.map change_of_alphabet)[d]? = none := by
            rw [List.getElem?_eq_none]; simp only [List.length_map]; omega
          rw [Turing.ListBlank.tail]
          simp only [Quotient.liftOn'_mk'', List.tail_cons]
          simp only [Turing.ListBlank.mk, Quotient.liftOn'_mk'', hnil, Option.getD_none]
          have : cfg.work (1 + ↑d) = (default : Γ') := by
            have := h_sim_work_blank_high (1 + d) (by rw [h_output_eq, h]; simp; omega)
            simp only [Nat.cast_add, Nat.cast_one] at this
            exact this
          rw [this]
    · intro d
      rw [h_sim_idx]
      unfold Turing.TM0.init Turing.Tape.mk₁
      simp only [zero_sub, Int.reduceNeg, Turing.ListBlank.nth, Turing.Tape.mk₂,
        Turing.Tape.mk'_left]
      exact h_sim_work_blank_low _ (by omega)
  obtain ⟨tm0HaltCfg, h_reaches, h_tm0_halt⟩ :=
    sim_steps_imply_tm0_steps change_of_alphabet M cfg
      (Turing.TM0.init (output.map change_of_alphabet)) output
      h_match h_computes_from_cfg h_output_eq
  unfold Turing.TM0.eval
  rw [Part.dom_iff_mem]
  use tm0HaltCfg.Tape.right₀
  rw [Part.mem_map_iff]
  use tm0HaltCfg
  constructor
  · rw [Turing.mem_eval]
    exact ⟨h_reaches, h_tm0_halt⟩
  · rfl

lemma language_recognised_by_tm0_subset_language_of_generator_from_tm0 {Γ Γ' Λ : Type u}
  [Inhabited Λ]
  [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S) :
  { input : List Γ | default ∉ input ∧ (Turing.TM0.eval M (input.map change_of_alphabet)).Dom }
  ⊆
  (generatedLanguage
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (generatorFromTM0_supports change_of_alphabet M S hS).choose
    (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).val := by
  intro input ⟨h_no_default, h_halts⟩
  exact anything_a_tm0_recognises_can_be_generated_by_its_generator
    change_of_alphabet hchange_default hchange_injective M S hS input h_no_default h_halts

lemma language_of_generator_from_tm0_subset_language_recognised_by_tm0 {Γ Γ' Λ : Type u}
  [Inhabited Λ]
  [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S) :
  (generatedLanguage
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (generatorFromTM0_supports change_of_alphabet M S hS).choose
    (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).val
  ⊆
  { input : List Γ | default ∉ input ∧ (Turing.TM0.eval M (input.map change_of_alphabet)).Dom }
:= by
  intro input h_generated
  have h_no_default : default ∉ input :=
    (generatedLanguage
      (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
      (generatorFromTM0_supports change_of_alphabet M S hS).choose
      (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).property input h_generated
  exact ⟨h_no_default, anything_a_generator_generates_is_recognised_by_its_tm0
    change_of_alphabet hchange_default hchange_injective M S hS input h_generated⟩

lemma language_of_tm0_eq_language_of_generator_from_tm0 {Γ Γ' Λ : Type u}
  [Inhabited Λ]
  [Inhabited Γ] [FinEnum Γ]
  [Inhabited Γ'] [FinEnum Γ']
  (change_of_alphabet : Γ → Γ')
  (hchange_default : change_of_alphabet default = default)
  (hchange_injective : Function.Injective change_of_alphabet)
  (M : Turing.TM0.Machine (Γ := Γ') (Λ := Λ))
  (S : Finset Λ)
  (hS : Turing.TM0.Supports M ↑S) :
  (generatedLanguage
    (generatorFromTM0 (enc_Γ := StandardEncoding Γ) change_of_alphabet M)
    (generatorFromTM0_supports change_of_alphabet M S hS).choose
    (generatorFromTM0_supports change_of_alphabet M S hS).choose_spec).val
  =
  { input : List Γ | default ∉ input ∧ (Turing.TM0.eval M (input.map change_of_alphabet)).Dom }
:= by
  apply Set.Subset.antisymm
  · exact language_of_generator_from_tm0_subset_language_recognised_by_tm0
      change_of_alphabet hchange_default hchange_injective M S hS
  · exact language_recognised_by_tm0_subset_language_of_generator_from_tm0
      change_of_alphabet hchange_default hchange_injective M S hS

end GenerationByTM0Simulation

end RandomisedGeneration
