import Mathlib

namespace RandomisedGeneration

structure Encoding (Γ : Type u) where
  W : ℕ
  W_pos : W > 0
  enum : Fin (2^W) → Option Γ
  complete : ∀ g : Γ, ∃ i, enum i = some g

/-- Standard encoding using FinEnum, which provides a computable enumeration. -/
def StandardEncoding (Γ : Type u) [Inhabited Γ] [FinEnum Γ] [DecidableEq Γ] : Encoding Γ where
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

abbrev WIDTH (Γ : Type u) [Inhabited Γ] [FinEnum Γ] [DecidableEq Γ] :=
  (StandardEncoding Γ).W

-- Helper function to get the i-th bit of a natural number in MSB-first order
-- For a W-bit encoding, bit 0 is the most significant, bit W-1 is the least significant
def getNthBitMSB (n : ℕ) (width : ℕ) (i : ℕ) : Bool :=
  if i < width then
    n.testBit (width - 1 - i)
  else
    false

-- Encode a symbol as its index in the finite enumeration
def symbolToNat {Γ : Type u} [FinEnum Γ] (g : Γ) : ℕ :=
  (FinEnum.equiv g).val

-- Get the k-th bit of the encoding of symbol g (MSB-first)
def getEncodingBit {Γ : Type u} [FinEnum Γ] (enc : Encoding Γ) (g : Γ) (k : ℕ) : Bool :=
  getNthBitMSB (symbolToNat g) enc.W k

-- The special "end of input" encoding
def getEOFBit {Γ : Type u} [Fintype Γ] (enc : Encoding Γ) (k : ℕ) : Bool :=
  getNthBitMSB (Fintype.card Γ) enc.W k

def bitstreamFromInput {Γ : Type u} [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
 (input : List Γ) : ℕ → Bool :=
  let enc := StandardEncoding Γ
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

def readBlockOfBitsNat
  (input : ℕ → Bool) (base offset : ℕ) : ℕ :=
  (Finset.range offset).sum (fun i =>
    (if input (base + i) then 1 else 0) * 2^(offset - i - 1))

lemma readBlockOfBits_lt_pow (input : ℕ → Bool) (base offset : ℕ) :
  readBlockOfBitsNat input base offset < 2^offset := by
  unfold readBlockOfBitsNat
  induction offset with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h_shift : ∀ i ∈ Finset.range n,
      (if input (base + i) then 1 else 0) * 2^(n + 1 - i - 1) =
      2 * ((if input (base + i) then 1 else 0) * 2^(n - i - 1)) := by
      intro i hi
      have hi' : i < n := by simpa using hi
      have : n + 1 - i - 1 = n - i := by omega
      rw [this, ← mul_assoc]
      ring_nf
      split_ifs
      · have : n - i - 1 + 1 = n - i := by omega
        rw [← this, pow_succ, mul_comm]
        simp [this]
      · simp
    rw [show ∑ i ∈ Finset.range n, (if input (base + i) then 1 else 0) * 2^(n + 1 - i - 1) =
            ∑ i ∈ Finset.range n, 2 * ((if input (base + i) then 1 else 0) * 2^(n - i - 1)) by
        apply Finset.sum_congr rfl
        exact h_shift]
    rw [← Finset.mul_sum]
    have h_last : n + 1 - n - 1 = 0 := by omega
    rw [h_last, pow_zero, mul_one]
    have h_bit : (if input (base + n) then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have h_sum : (Finset.range n).sum (fun i =>
      (if input (base + i) then 1 else 0) * 2^(n - i - 1)) ≤ 2^n - 1 := by
      cases Nat.eq_zero_or_pos n with
      | inl hn =>
        subst hn
        simp
      | inr hn =>
        have : (Finset.range n).sum (fun i =>
          (if input (base + i) then 1 else 0) * 2^(n - i - 1)) < 2^n := ih
        omega
    calc 2 * (Finset.range n).sum (fun i => (if input (base + i) then 1 else 0) * 2^(n - i - 1))
          + (if input (base + n) then 1 else 0)
        ≤ 2 * (2^n - 1) + 1 := by omega
      _ = 2^(n + 1) - 1 := by
          rw [pow_succ]
          omega
      _ < 2^(n + 1) := by omega

lemma readBlockOfBitsNat_succ (input : ℕ → Bool) (base x : ℕ) :
  readBlockOfBitsNat input base (x + 1) =
  2 * readBlockOfBitsNat input base x + (if input (base + x) then 1 else 0) := by
  unfold readBlockOfBitsNat
  rw [Finset.sum_range_succ]
  have h_shift : ∀ i ∈ Finset.range x,
    (if input (base + i) then 1 else 0) * 2^(x + 1 - i - 1) =
    2 * ((if input (base + i) then 1 else 0) * 2^(x - i - 1)) := by
    intro i hi
    have hi' : i < x := by simpa using hi
    have h1 : x + 1 - i - 1 = x - i := by omega
    have h2 : x - i - 1 + 1 = x - i := by omega
    split_ifs
    · rw [h1, ← h2, pow_succ]
      ring_nf
      have : 1 + (x - i - 1) - 1 = x - i - 1 := by omega
      rw [this]
    · simp
  rw [show ∑ i ∈ Finset.range x, (if input (base + i) then 1 else 0) * 2^(x + 1 - i - 1) =
          ∑ i ∈ Finset.range x, 2 * ((if input (base + i) then 1 else 0) * 2^(x - i - 1)) by
      apply Finset.sum_congr rfl
      exact h_shift]
  rw [← Finset.mul_sum]
  have : x + 1 - x - 1 = 0 := by omega
  rw [this, pow_zero, mul_one]

def readBlockOfBitsW
  (input : ℕ → Bool) (base : ℕ) (x : ℕ) (W : ℕ)
  (hx : x ≤ W) :
  Fin (2^W) :=
⟨
  readBlockOfBitsNat input base x,
  by
    have h := readBlockOfBits_lt_pow input base x
    -- now use hx to lift bound
    have : 2^x ≤ 2^W :=
      Nat.pow_le_pow_right (by norm_num) hx
    exact lt_of_lt_of_le h this
⟩

lemma sum_testBit_eq {n W : ℕ} (h : n < 2 ^ W) :
  (Finset.range W).sum (fun i => (if n.testBit i then 1 else 0) * 2^i) = n := by
  induction W generalizing n
  case zero =>
    -- W = 0, sum over empty range is 0, n < 1 ⇒ n = 0
    simp at h
    simp [h]
  case succ W' ih =>
    rw [Finset.sum_range_succ]
    conv_rhs => rw [← Nat.div_add_mod n (2^W')]
    rw [add_comm (2^W' * (n / 2^W')) (n % 2^W')]
    congr 1
    · convert ih (Nat.mod_lt n (Nat.pow_pos (by omega : 0 < 2))) using 3
      simp only [Nat.testBit_mod_two_pow]
      split_ifs with h1 h2
      · rfl
      · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and, Bool.not_eq_true] at h2
        rename_i x hx
        have h3 : x < W' := Finset.mem_range.mp hx
        have h4 : n.testBit x = false := h2 h3
        rw [h1] at h4
        exact Bool.noConfusion h4
      · simp only [Bool.not_eq_true] at h1
        rename_i x hx h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        have h3 : n.testBit x = true := h2.2
        rw [h1] at h3
        exact Bool.noConfusion h3
      · rfl
    · by_cases hbit : n.testBit W' = true
      · simp only [hbit, ↓reduceIte, one_mul, ne_eq,
        Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
        not_false_eq_true, left_eq_mul₀]
        simp only [Nat.testBit] at hbit
        have h_bound : n / 2 ^ W' < 2 := by
          have : 2 ^ (W' + 1) = 2 * 2 ^ W' := by ring
          rw [this] at h
          apply Nat.div_lt_of_lt_mul
          · omega
        have : (n / 2 ^ W') % 2 = 1 := by
          have h_shift : n >>> W' = n / 2 ^ W' := Nat.shiftRight_eq_div_pow n W'
          rw [← h_shift]
          have : 1 &&& (n >>> W') = 1 := by
            have : 1 &&& (n >>> W') ≠ 0 := by simpa using hbit
            -- rewrite the shift into division
            rw [h_shift] at this ⊢
            -- let m = n / 2 ^ W'
            set m := n / 2 ^ W' with hm
            -- now rewrite everything in terms of m
            simp only [hm, Nat.one_and_eq_mod_two, ne_eq, Nat.mod_two_not_eq_zero] at this h_bound ⊢
            -- from m < 2 we know m = 0 ∨ m = 1
            have hm_cases : m = 0 ∨ m = 1 := by
              rw [←hm] at h_bound
              -- First, note that m < 2
              have h : m < 2 := h_bound
              -- Now, since m : ℕ, the only possibilities are 0 or 1
              cases h : m with
              | zero => exact Or.inl rfl
              | succ m' =>
                right
                have : m' < 1 := by
                  have : m = m' + 1 := h
                  omega
                simp only [Nat.lt_one_iff] at this
                rw [this]
            cases hm_cases with
            | inl h0 =>
                -- m = 0 contradicts nonzero bit
                rw [← hm] at this
                rw [h0] at this
                simp at this
            | inr h1 =>
                -- m = 1 gives the goal
                rw [← hm]
                rw [h1]
          simp only [Nat.one_and_eq_mod_two] at this
          exact this
        interval_cases n / 2 ^ W'
        · simp at this
        · rfl
      · simp only [hbit, Bool.false_eq_true, ↓reduceIte, zero_mul,
                zero_eq_mul, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
                false_and, Nat.div_eq_zero_iff, false_or]
        have h_n_div_2w_mod_2_eq_0 : n / 2 ^ W' % 2 = 0 := by
          have : n.testBit W' = false := by simp_all
          unfold Nat.testBit at this
          simp only [Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero, beq_eq_false_iff_ne,
            ne_eq, Nat.mod_two_not_eq_one] at this
          omega
        have h_n_div_2_w_even : Even (n / 2 ^ W') := by
          rw [even_iff_two_dvd]
          exact Nat.dvd_of_mod_eq_zero h_n_div_2w_mod_2_eq_0
        have h_n_div_2W_lt_2 : n / 2 ^ W' < 2 := by
          have : n < 2 * 2 ^ W' := by calc n < 2 ^ (W' + 1) := h
                                          _ = 2 * 2 ^ W' := by ring
          have h_pow_pos : 0 < 2 ^ W' := Nat.pow_pos (by omega : 0 < 2)
          rw [Nat.div_lt_iff_lt_mul h_pow_pos]
          exact this
        have h_n_div_2W_eq_0 : n / 2 ^ W' = 0 := by
          -- n / 2^W' is even and n / 2^W' < 2
          -- So n / 2^W' ∈ {0, 1} and even, therefore must be 0
          interval_cases n / 2 ^ W'
          · rfl
          · -- Case n / 2^W' = 1, contradicts evenness
            exfalso
            rw [even_iff_two_dvd] at h_n_div_2_w_even
            have : ¬(2 ∣ 1) := by omega
            contradiction
        have : n = n % 2 ^ W' := by
          rw [← Nat.div_add_mod n (2 ^ W'), h_n_div_2W_eq_0]; simp
        rw [this]
        exact Nat.mod_lt n (Nat.pow_pos (by omega))

/-- Reindex sum from MSB-first to LSB-first order -/
lemma sum_reindex_msb_lsb {W : ℕ} (f : ℕ → ℕ) :
  (Finset.range W).sum (fun i => f (W - 1 - i) * 2 ^ (W - 1 - i)) =
  (Finset.range W).sum (fun j => f j * 2 ^ j) := by
  cases W with
  | zero => simp
  | succ W' =>
    rw [← Finset.sum_bij (fun i _ => W' - i)]
    · intro i hi
      simp only [Finset.mem_range] at hi ⊢
      omega
    · intro i hi
      simp only [Finset.mem_range] at hi
      intro a₂ ha₂ heq
      simp only [Finset.mem_range] at ha₂
      omega
    · intro b hb
      use W' - b
      simp only [Finset.mem_range] at hb ⊢
      constructor
      · omega
      · omega
    · intro j hj
      congr 1
      · congr 1
        simp only [Finset.mem_range] at hj
        omega
      · congr 1
        simp only [Finset.mem_range] at hj
        have hj' : j ≤ W' := Nat.lt_succ_iff.mp hj
        omega

lemma readBlockOfBits_decodes_to_EOF {Γ : Type u}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) :
  readBlockOfBitsNat
    (bitstreamFromInput input)
    ((WIDTH Γ) * input.length)
    (WIDTH Γ)
  = Fintype.card Γ := by
  unfold readBlockOfBitsNat bitstreamFromInput WIDTH StandardEncoding
  simp only []
  set W := (StandardEncoding Γ).W
  set card := Fintype.card Γ
  -- All bits we read are in the EOF region
  have h_bits : ∀ i < W,
    (if h : W * input.length + i < input.length * W then
      getEncodingBit (StandardEncoding Γ)
        (input.get ⟨(W * input.length + i) / W, Nat.div_lt_iff_lt_mul
        (StandardEncoding Γ).W_pos |>.mpr h⟩)
        ((W * input.length + i) % W)
    else if W * input.length + i < (input.length + 1) * W then
      getEOFBit (StandardEncoding Γ) ((W * input.length + i) % W)
    else false) = getEOFBit (StandardEncoding Γ) i := by
    intro i hi
    have h1 : ¬(W * input.length + i < input.length * W) := by
      simp
      linarith
    have h2 : W * input.length + i < (input.length + 1) * W := by
      calc W * input.length + i
          < W * input.length + W := by omega
        _ = (input.length + 1) * W := by ring
    have h3 : (W * input.length + i) % W = i := by
      rw [Nat.add_mod, Nat.mul_mod_right]
      simp only [zero_add, dvd_refl, Nat.mod_mod_of_dvd]
      exact Nat.mod_eq_of_lt hi
    simp [h1, h2, h3]
  simp only [StandardEncoding, W] at h_bits ⊢
  -- Rewrite using h_bits
  have : ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (if h : (FinEnum.card Γ).size * input.length + x <
        input.length * (FinEnum.card Γ).size then
            getEncodingBit
              { W := (FinEnum.card Γ).size,
                W_pos := (StandardEncoding Γ).W_pos,
                enum := fun i ↦ if h : ↑i < FinEnum.card Γ then
                  some (FinEnum.equiv.symm ⟨↑i, h⟩) else none,
                complete := (StandardEncoding Γ).complete }
              (input.get ⟨((FinEnum.card Γ).size * input.length + x) / (FinEnum.card Γ).size,
                Nat.div_lt_iff_lt_mul (StandardEncoding Γ).W_pos |>.mpr h⟩)
              (((FinEnum.card Γ).size * input.length + x) % (FinEnum.card Γ).size)
          else if (FinEnum.card Γ).size * input.length + x <
            (input.length + 1) * (FinEnum.card Γ).size then
            getEOFBit (Γ := Γ)
              { W := (FinEnum.card Γ).size,
                W_pos := (StandardEncoding Γ).W_pos,
                enum := fun i ↦ if h : ↑i < FinEnum.card Γ then
                  some (FinEnum.equiv.symm ⟨↑i, h⟩) else none,
                complete := (StandardEncoding Γ).complete }
              (((FinEnum.card Γ).size * input.length + x) % (FinEnum.card Γ).size)
          else false) = true then 1 else 0) * 2 ^ ((FinEnum.card Γ).size - x - 1) =
    ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if getEOFBit (Γ := Γ)
            { W := (FinEnum.card Γ).size,
              W_pos := (StandardEncoding Γ).W_pos,
              enum := fun i ↦ if h : ↑i < FinEnum.card Γ then
                some (FinEnum.equiv.symm ⟨↑i, h⟩) else none,
              complete := (StandardEncoding Γ).complete }
            x = true then 1 else 0) * 2 ^ ((FinEnum.card Γ).size - x - 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_range] at hx
    congr 1
    congr 1
    rw [h_bits x hx]
  rw [this]
  clear this
  -- Simplify getEOFBit
  unfold getEOFBit getNthBitMSB
  simp only []
  -- Simplify: inside the sum, x < (FinEnum.card Γ).size is always true
  have h_simp : ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (if x < (FinEnum.card Γ).size then
            (Fintype.card Γ).testBit ((FinEnum.card Γ).size - 1 - x)
          else false) = true then 1 else 0) * 2 ^ ((FinEnum.card Γ).size - x - 1) =
    ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (Fintype.card Γ).testBit ((FinEnum.card Γ).size - 1 - x) then 1 else 0) *
      2 ^ ((FinEnum.card Γ).size - x - 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    simp [hx]
  rw [h_simp]
  clear h_simp
  -- Apply the reindexing lemma
  have : ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (Fintype.card Γ).testBit ((FinEnum.card Γ).size - 1 - x) = true then 1 else 0) *
      2 ^ ((FinEnum.card Γ).size - x - 1) =
    ∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (Fintype.card Γ).testBit x = true then 1 else 0) * 2 ^ x := by
    set W := (FinEnum.card Γ).size
    set n := Fintype.card Γ
    -- Use Finset.sum_bij to establish the bijection i ↦ W - 1 - i
    refine Finset.sum_bij (fun i _ => W - 1 - i) ?_ ?_ ?_ ?_
    · intro i hi
      simp at hi ⊢
      omega
    · intro i₁ hi₁ i₂ hi₂ heq
      simp at hi₁ hi₂ heq
      omega
    · intro b hb
      use W - 1 - b
      simp at hb ⊢
      omega
    · simp only [Finset.mem_range, ite_mul, one_mul, zero_mul]
      intro a ha
      congr 2
      omega
  rw [this]
  clear this
  simp only [ite_mul, one_mul, zero_mul]
  -- The sum can be rewritten using the testBit characterization
  have : (∑ x ∈ Finset.range (FinEnum.card Γ).size,
      if (Fintype.card Γ).testBit x = true then 2 ^ x else 0) =
    (∑ x ∈ Finset.range (FinEnum.card Γ).size,
      (if (Fintype.card Γ).testBit x then 1 else 0) * 2 ^ x) := by
    congr 1
    ext x
    by_cases h : (Fintype.card Γ).testBit x
    · simp [h]
    · simp [h]
  rw [this]
  clear this
  have h_bound : card < 2^(FinEnum.card Γ).size := by
    change Fintype.card Γ < 2 ^ (FinEnum.card Γ).size
    rw [← FinEnum.card_eq_fintypeCard]
    exact Nat.lt_size_self (FinEnum.card Γ)
  exact sum_testBit_eq h_bound

lemma bitstreamFromInput_in_range {Γ : Type u}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) (i : ℕ) (hi : i < input.length * (WIDTH Γ)) :
  bitstreamFromInput input i =
  getEncodingBit (StandardEncoding Γ)
    (input.get ⟨i / (WIDTH Γ), Nat.div_lt_iff_lt_mul (StandardEncoding Γ).W_pos |>.mpr hi⟩)
    (i % (WIDTH Γ)) := by
  unfold bitstreamFromInput WIDTH
  simp [hi]

lemma readBlockOfBits_extracts_symbol {Γ : Type u}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) {k : ℕ} (hk : k < input.length) :
  (Finset.range (WIDTH Γ)).sum (fun i =>
    (if bitstreamFromInput input ((WIDTH Γ) * k + i) then 1 else 0) *
    2^((WIDTH Γ) - 1 - i)) = symbolToNat (input.get ⟨k, hk⟩) := by
  set W := WIDTH Γ
  set g := input.get ⟨k, hk⟩
  -- All bits are in the input range
  have h_in_range : ∀ i < W, W * k + i < input.length * W := by
    intro i hi
    calc W * k + i
        < W * k + W := by omega
      _ = W * (k + 1) := by ring
      _ ≤ W * input.length := by exact Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hk)
      _ = input.length * W := by exact Nat.mul_comm  W input.length
  -- Each bit comes from the encoding of g
  have h_bits : ∀ i < W,
    bitstreamFromInput input (W * k + i) = getEncodingBit (StandardEncoding Γ) g i := by
    intro i hi
    rw [bitstreamFromInput_in_range input (W * k + i) (h_in_range i hi)]
    congr
    · -- (W * k + i) / W = k
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ (StandardEncoding Γ).W_pos]
      simp only [Nat.add_eq_right, Nat.div_eq_zero_iff]
      right
      exact hi
    · -- (W * k + i) % W = i
      rw [Nat.add_mod, Nat.mul_mod_right]
      simp only [zero_add, dvd_refl, Nat.mod_mod_of_dvd]
      exact Nat.mod_eq_of_lt hi
  -- Rewrite sum using h_bits
  have h_sum_rewrite : ∑ i ∈ Finset.range W,
      (if bitstreamFromInput input (W * k + i) = true then 1 else 0) * 2 ^ (W - 1 - i) =
    ∑ i ∈ Finset.range W,
      (if getEncodingBit (StandardEncoding Γ) g i = true then 1 else 0) * 2 ^ (W - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 2
    have h := h_bits i hi
    simp [h]
  rw [h_sum_rewrite]
  -- Expand definitions
  unfold getEncodingBit getNthBitMSB symbolToNat
  set n := (FinEnum.equiv g).val
  -- Simplify conditions (all i in range satisfy i < W)
  have h_simp : ∑ i ∈ Finset.range W,
      (if (if i < W then n.testBit (W - 1 - i) else false) = true then 1 else 0) * 2 ^ (W - 1 - i) =
    ∑ i ∈ Finset.range W,
      (if n.testBit (W - 1 - i) then 1 else 0) * 2 ^ (W - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    simp [hi]
  rw [h_simp]
  -- Reindex MSB to LSB
  have h_reindex : ∑ x ∈ Finset.range W,
      (if n.testBit (W - 1 - x) then 1 else 0) * 2 ^ (W - 1 - x) =
    ∑ x ∈ Finset.range W,
      (if n.testBit x then 1 else 0) * 2 ^ x := by
    refine Finset.sum_bij (fun i _ => W - 1 - i) ?_ ?_ ?_ ?_
    · intro i hi; simp at hi ⊢; omega
    · intro i₁ hi₁ i₂ hi₂ heq; simp at hi₁ hi₂ heq; omega
    · intro b hb; use W - 1 - b; simp at hb ⊢; omega
    · simp only [Finset.mem_range, ite_mul, one_mul, zero_mul]
      intro a ha
      trivial
  rw [h_reindex]
  -- Apply binary representation lemma
  have h_bound : n < 2^W := by
    have : n < FinEnum.card Γ := (FinEnum.equiv g).2
    calc n < FinEnum.card Γ := this
         _ < 2^(Nat.size (FinEnum.card Γ)) := Nat.lt_size_self _
         _ = 2^W := rfl
  exact sum_testBit_eq h_bound

lemma readBlockOfBits_decodes_to_input {Γ : Type u}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) {k : ℕ} (hk : k < input.length) :
  (StandardEncoding Γ).enum (
    readBlockOfBitsW
      (bitstreamFromInput input)
      ((WIDTH Γ) * k)
      (WIDTH Γ)
      (WIDTH Γ)
      (by omega)
  ) = some (input.get ⟨k, hk⟩) := by
  unfold readBlockOfBitsW
  simp only [List.get_eq_getElem]
  set W := WIDTH Γ
  set g := input.get ⟨k, hk⟩
  have h_val : readBlockOfBitsNat (bitstreamFromInput input) (W * k) W = symbolToNat g := by
    unfold readBlockOfBitsNat
    convert readBlockOfBits_extracts_symbol input hk using 2
    · simp only [show W = WIDTH Γ from rfl]
      congr 2
      omega
  -- Unfold StandardEncoding.enum
  unfold StandardEncoding
  simp only
  -- symbolToNat g is in range
  have h_lt : symbolToNat g < FinEnum.card Γ := (FinEnum.equiv g).2
  simp only [Option.dite_none_right_eq_some, Option.some.injEq]
  refine ⟨?_, ?_⟩
  · convert h_lt using 1
  · suffices FinEnum.equiv.symm ⟨symbolToNat g, h_lt⟩ = g by
      convert this using 1
      congr
    unfold symbolToNat
    exact Equiv.symm_apply_apply (FinEnum.equiv) g

lemma EOF_enum_is_none {Γ : Type u}
  [Inhabited Γ] [Fintype Γ] [FinEnum Γ] [DecidableEq Γ]
  (input : List Γ) :
  (StandardEncoding Γ).enum
    (readBlockOfBitsW
      (bitstreamFromInput input)
      (WIDTH Γ * input.length)
      (WIDTH Γ)
      (WIDTH Γ)
      (by omega))
  = none := by
  -- unfold readBlockOfBitsW
  simp only [readBlockOfBitsW]
  -- readBlockOfBitsW wraps readBlockOfBitsNat in a `Fin 2^W`, so we look at the value
  have hval := readBlockOfBits_decodes_to_EOF input
  -- By definition of StandardEncoding.enum, indices ≥ card Γ map to none
  unfold StandardEncoding
  simp only [dite_eq_right_iff, reduceCtorEq, imp_false, not_lt, ge_iff_le]
  -- Fintype.card Γ < 2^WIDTH Γ by Nat.size definition
  -- So the 'if' in enum fails and gives none
  rw [hval]
  have h_card : FinEnum.card Γ = Fintype.card Γ := FinEnum.card_eq_fintypeCard
  omega

end RandomisedGeneration
