import data.nat.basic

example : ∀ x ≤ 5, ∀ y ≤ 5, x * y ≠ 23 :=
dec_trivial