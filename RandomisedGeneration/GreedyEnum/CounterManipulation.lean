import Mathlib

namespace RandomisedGeneration

universe u

namespace GreedyEnum

def counterToInput (counter : List (ULift.{u} Bool)) : ℕ → Bool :=
  fun i => match counter[i]? with
    | some b => b.down
    | none   => false

def counterIncrement : List (ULift.{u} Bool) → List (ULift.{u} Bool)
  | [] => [ULift.up true]
  | ⟨false⟩ :: rest => ⟨true⟩ :: rest
  | ⟨true⟩ :: rest => ⟨false⟩ :: counterIncrement rest

/-- The natural number represented by a counter (LSB first). -/
def counterToNat : List (ULift.{u} Bool) → ℕ
  | [] => 0
  | ⟨b⟩ :: rest => (if b then 1 else 0) + 2 * counterToNat rest

lemma counterToNat_increment (c : List (ULift.{u} Bool)) :
    counterToNat (counterIncrement c) = counterToNat c + 1 := by
  induction c with
  | nil => simp [counterIncrement, counterToNat]
  | cons b rest ih =>
    cases b with | up bv =>
    cases bv <;> simp [counterIncrement, counterToNat, ih] <;> ring

/-- The n-th counter value produced by repeated increment from []. -/
def counterIterN : ℕ → List (ULift.{u} Bool)
  | 0 => []
  | n + 1 => counterIncrement (counterIterN n)

lemma counterIterN_toNat (n : ℕ) :
    counterToNat (counterIterN n) = n := by
  induction n with
  | zero => simp [counterIterN, counterToNat]
  | succ n ih => simp [counterIterN, counterToNat_increment, ih]

/-- counterToInput reads bit i as Nat.testBit of the counter's natural value. -/
lemma counterToInput_eq_testBit (c : List (ULift.{u} Bool)) (i : ℕ) :
    counterToInput c i = Nat.testBit (counterToNat c) i := by
  induction c generalizing i with
  | nil => simp [counterToInput, counterToNat]
  | cons b rest ih =>
    cases b with | up bv =>
    simp only [counterToInput, counterToNat]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero]
      cases bv <;> simp [Nat.testBit_zero]
    | succ i =>
      simp only [List.getElem?_cons_succ]
      change counterToInput rest i = _
      rw [ih]
      cases bv <;> simp [Nat.testBit_succ, Nat.add_mul_div_left _ _ (by omega : 0 < 2)]

lemma counterToInput_counterIterN (n : ℕ) (i : ℕ) :
    counterToInput (counterIterN n) i = Nat.testBit n i := by
  rw [counterToInput_eq_testBit, counterIterN_toNat]

/-- A counter representing a value ≥ 2^k has length ≥ k + 1. -/
lemma counterToNat_length_bound (c : List (ULift.{u} Bool)) (k : ℕ)
    (h : counterToNat c ≥ 2 ^ k) : c.length ≥ k + 1 := by
  induction k generalizing c with
  | zero =>
    cases c with
    | nil => simp [counterToNat] at h
    | cons _ _ => simp
  | succ k ih =>
    cases c with
    | nil => simp [counterToNat] at h
    | cons b rest =>
      cases b with | up bv =>
      simp only [counterToNat, List.length_cons] at h ⊢
      have : counterToNat rest ≥ 2 ^ k := by
        cases bv <;> simp at h <;> omega
      exact Nat.succ_le_succ (ih rest this)

lemma counterIterN_length_ge (n k : ℕ) (h : n ≥ 2 ^ k) :
    (counterIterN n).length ≥ k + 1 :=
  counterToNat_length_bound _ k (by rw [counterIterN_toNat]; exact h)

end GreedyEnum

end RandomisedGeneration
