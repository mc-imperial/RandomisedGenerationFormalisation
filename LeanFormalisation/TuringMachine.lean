import Mathlib

inductive Direction
  | L     -- move left
  | R     -- move right
  | N     -- stay / no move

instance : Coe Direction ℤ :=
⟨fun
  | Direction.L => -1
  | Direction.N => 0
  | Direction.R => 1⟩

structure TM (Sigma Q : Type*) [Fintype Sigma] [Fintype Q] where
  init : Q -- Initial state
  accept : Q -- Accepting state
  reject : Q -- Rejecting state
  accept_ne_reject : accept ≠ reject
  δ : Q → Option Sigma → Q × Option Sigma × Direction -- Transition function (curried)
  loop_on_accept : ∀ a : Option Sigma, δ accept a = (accept, a, Direction.N)
  loop_on_reject : ∀ a : Option Sigma, δ reject a = (reject, a, Direction.N)

def Tape (Sigma : Type*) := ℤ → Option Sigma

def initial_tape (Sigma : Type*) (input : List Sigma) : Tape Sigma :=
  fun (i: ℤ) =>
    if i < 0 then
      none
    else
      let j : ℕ := Int.toNat i
      if h' : j < input.length then
        input.get ⟨j, h'⟩
      else
        none

structure TM_config (Sigma Q : Type*) [Fintype Sigma] [Fintype Q] where
  state : Q
  tape : Tape Sigma
  head : ℤ

attribute [ext] TM_config

def step {Sigma Q : Type*} [Fintype Sigma] [Fintype Q] (M : TM Sigma Q) (c : TM_config Sigma Q)
      : TM_config Sigma Q :=
  let (successor, written_symbol, direction) := M.δ c.state (c.tape c.head)
  let new_tape : Tape Sigma := fun i => if (i = c.head) then written_symbol else c.tape i
  {state := successor, tape := new_tape, head := c.head + direction}

def run {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) : ℕ → TM_config Sigma Q
    | 0 => {state := M.init, tape := initial_tape Sigma input, head := 0}
    | n + 1 => step M (run M input n)

lemma step_sticks_on_state {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
  (M : TM Sigma Q) (q : Q) (c : TM_config Sigma Q)
  (loop : ∀ a : Option Sigma, M.δ q a = (q, a, Direction.N))
  (hq : c.state = q) :
  step M c = c := by
  ext
  case state => simp [step, hq, loop]
  case head  => simp [step, hq, loop]
  case tape  =>
    funext i
    simp only [step, hq, loop, add_zero, ite_eq_right_iff]
    intro h'
    rw [h']

lemma step_sticks_on_accept {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
  (M : TM Sigma Q) (c : TM_config Sigma Q) :
  c.state = M.accept → step M c = c :=
  fun h => step_sticks_on_state M M.accept c M.loop_on_accept h

lemma step_sticks_on_reject {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
  (M : TM Sigma Q) (c : TM_config Sigma Q) :
  c.state = M.reject → step M c = c :=
  fun h => step_sticks_on_state M M.reject c M.loop_on_reject h

lemma run_sticks_on_state {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) (q : Q)
    (step_sticks : ∀ c : TM_config Sigma Q, c.state = q → step M c = c):
    ∀ i : ℕ, (run M input i).state = q →
    ∀ j ≥ i, (run M input j).state = q :=
by
  intro i h_i j hji
  let k := j - i
  have h_k_eq_j_minus_i : k = j - i := by rfl
  have h_j_eq_i_plus_k : j = i + k := by
    rw [h_k_eq_j_minus_i]
    rw [eq_comm]
    rw [Nat.add_sub_of_le hji]
  rw [h_j_eq_i_plus_k]
  induction k with
  | zero =>
      rw [Nat.add_zero]
      exact h_i
  | succ k ih =>
      dsimp [run]
      have h_step_eq : step M (run M input (i + k)) = run M input (i + k) :=
  step_sticks (run M input (i + k)) ih
      have h_state_eq : (step M (run M input (i + k))).state = (run M input (i + k)).state :=
  congrArg TM_config.state h_step_eq
      simp [ih, h_state_eq]

theorem run_sticks_on_accept {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) :
    ∀ i : ℕ, (run M input i).state = M.accept →
    ∀ j ≥ i, (run M input j).state = M.accept :=
    run_sticks_on_state M input M.accept (step_sticks_on_accept M)

theorem run_sticks_on_reject {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) :
    ∀ i : ℕ, (run M input i).state = M.reject →
    ∀ j ≥ i, (run M input j).state = M.reject :=
    run_sticks_on_state M input M.reject (step_sticks_on_reject M)

def accepts {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) : Prop := ∃ i : ℕ, ((run M input) i).state = M.accept

def rejects {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) : Prop := ∃ i : ℕ, ((run M input) i).state = M.reject

def loops {Sigma Q : Type*} [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (input : List Sigma) : Prop :=
    ∀ i : ℕ,
    (run M input i).state ≠ M.accept ∧
    (run M input i).state ≠ M.reject

def valid_tape (Sigma : Type*) (t : Tape Sigma) : Prop :=
  ∃ i j : ℤ, i ≤ j ∧ (∀ k, k ≤ i → t k = none) ∧ (∀ k, k ≥ j → t k = none)

theorem initial_tape_valid (Sigma : Type*) (input : List Sigma) :
  valid_tape Sigma (initial_tape Sigma input) := by
    let t : Tape Sigma := initial_tape Sigma input
    let i : ℤ := -1
    let j : ℤ := input.length
    have h_jgeq0 : j ≥ 0 := by exact Int.natCast_nonneg input.length
    have h_ileqj : i ≤ j := by linarith
    have h_below_i_blank : (∀ k, k ≤ i → t k = none) := by
      intro k hk
      have h_klt0 : (k < 0) := by linarith
      have h_tkblank : (t k = none) := by
        simp [t, initial_tape, h_klt0]
      exact h_tkblank
    have h_above_j_blank : ∀ k, k ≥ j → t k = none := by
      intro k hk
      have h_kge0 : k ≥ 0 := by linarith
      have h_not_lt : ¬ k.toNat < input.length := by
        have h_jeqinputlength : j.toNat = input.length := by simp [j]
        have h_kgeqj : k.toNat ≥ j.toNat := by
          apply Int.toNat_le_toNat
          exact hk
        have h_kgeqinputlength : k.toNat ≥ input.length := by linarith
        exact Nat.not_lt_of_ge h_kgeqinputlength
      simp [t, initial_tape, h_not_lt]
    have h : valid_tape Sigma t := by exact ⟨i, j, h_ileqj, h_below_i_blank, h_above_j_blank⟩
    exact h

theorem step_preserves_validity (Sigma Q : Type*) [Fintype Sigma] [Fintype Q]
    (M : TM Sigma Q) (c : TM_config Sigma Q) :
         valid_tape Sigma c.tape → valid_tape Sigma (step M c).tape := by
    intro hvalid
    rcases hvalid with ⟨i, j, hle, hleft, hright⟩
    let t' := (step M c).tape
    have hsame : ∀ k, k ≠ c.head → c.tape k = t' k := by
      intro k hk
      dsimp [t']
      unfold step
      simp only [if_neg hk]
    let i' := min i (c.head - 1)
    let j' := max j (c.head + 1)
    -- i' ≤ i
    have hi : i' ≤ i := min_le_left i (c.head - 1)
    -- j ≤ j'
    have hj : j ≤ j' := le_max_left j (c.head + 1)
    have h_ileqj' : i' ≤ j' := by
      -- combine
      exact hi.trans (hle.trans hj)
    have h_i_lt_head : i' < c.head := by
      have : i' ≤ c.head - 1 := min_le_right i (c.head - 1)
      linarith
    have h_j_gt_head : j' > c.head := by
      have : j' ≥ c.head + 1 := le_max_right j (c.head + 1)
      linarith
    have h_blank_below_i' : ∀ k, k ≤ i' → t' k = none := by
      intro k hk
      have hk_le_i : k ≤ i := le_trans hk hi
      have hk_ne_head : k ≠ c.head :=
        ne_of_lt (lt_of_le_of_lt hk h_i_lt_head)
      calc
        t' k = c.tape k := (hsame k hk_ne_head).symm
        _    = none    := hleft k hk_le_i
    have h_blank_above_j' : ∀ k, k ≥ j' → t' k = none := by
      intro k hk
      have hk_ge_j : k ≥ j := le_trans hj hk
      have hk_ne_head : k ≠ c.head :=
        ne_of_gt (lt_of_lt_of_le h_j_gt_head hk)
      calc
        t' k = c.tape k := (hsame k hk_ne_head).symm
        _    = none     := hright k hk_ge_j
    exact ⟨i', j', h_ileqj', h_blank_below_i', h_blank_above_j'⟩


namespace initial_tape_tests

def blank := '□'
def input_data : List Char := ['a','b','c']

def tape := initial_tape Char input_data

example : tape (-2) = none := rfl
example : tape (-1) = none := rfl
example : tape 0 = 'a' := rfl
example : tape 1 = 'b' := rfl
example : tape 2 = 'c' := rfl
example : tape 3 = none := rfl
example : tape 10 = none := rfl

end initial_tape_tests




def FormalLanguage (Sigma : Type*) := Set (List Sigma)

def RE (Sigma : Type*) [Fintype Sigma] : Set (FormalLanguage Sigma) :=
  { L | ∃ (Q : Type*) (_ : Fintype Q) (M : TM Sigma Q), ∀ x : List Sigma, L x ↔ accepts M x }
