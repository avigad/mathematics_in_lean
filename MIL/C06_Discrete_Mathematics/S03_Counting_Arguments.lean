import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Vector.Basic

import Mathlib.Data.Fintype.BigOperators

open Finset

section
variable {α : Type*} [Fintype α]

example (n : ℕ) : Fintype.card (Fin n → α) = (Fintype.card α)^n := by
  simp

example (n : ℕ) : Fintype.card (Mathlib.Vector α n) = (Fintype.card α)^n :=
by simp

end

#check Disjoint

example (m : ℕ) (h : m ≥ n) : card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint]
  · rw [card_range, card_image_of_injective]
    · rw [card_range]; omega
    apply add_right_injective
  rw [disjoint_iff_ne]
  simp; intro i j; omega

example (n : ℕ) : card ((range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2)) =
    n * (n + 1) / 2 := by
  have : (range (n+1) ×ˢ range (n+1)).filter (fun p => p.1 < p.2) =
    (range (n+1)).biUnion (fun j : ℕ => (range j).image fun i => (i, j)) := by
      simp [Finset.ext_iff, Prod.ext_iff, @and_left_comm _ (_ = _),
        iff_true_intro lt_trans]
  rw [this, Finset.card_biUnion]; swap
  · intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  transitivity (∑ i in range (n+1), i)
  · congr; ext i
    rw [Finset.card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [Finset.sum_range_id]; simp [mul_comm]

section
open Classical
variable (s t : Finset Nat) (a b : Nat)

#check Finset.sum_boole

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
  (r : α → β → Prop)
  (h_left : ∀ a ∈ s, 3 ≤ card (t.filter (r a ·)))
  (h_right : ∀ b ∈ t, card (s.filter (r · b)) = 1) :
    3 * s.card ≤ t.card := by
  calc
    3 * s.card = ∑ a ∈ s, 3 := by simp [sum_const_nat, mul_comm]
    _ ≤ ∑ a ∈ s, (t.filter (r a ·)).card := by
        exact sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by
        congr; simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := by
        exact sum_comm
    _ = ∑ b ∈ t, (s.filter (r · b)).card := by
        simp only [sum_boole, Nat.cast_id]
    _ = ∑ b ∈ t, 1 := by
        -- congr; ext b; apply h_right
        apply Finset.sum_congr rfl h_right
    _ ≤ t.card := by simp

section
theorem Nat.coprime_self_add_one (n : ℕ) : Nat.Coprime n (n + 1) := by simp only [coprime_self_add_right,
  coprime_one_right_eq_true]

example {n : ℕ} (A : Finset ℕ)
  (hA : A.card = n + 1)
  (hA' : A ⊆ Finset.range (2 * n)) :
    ∃ x y, x ∈ A ∧ y ∈ A ∧ Nat.Coprime x y := by
sorry

end
