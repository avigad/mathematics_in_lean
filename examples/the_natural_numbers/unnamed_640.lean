example (m n : ℕ) (f : ℕ → ℕ) : f (m * 1 + 0 + n) = f (m + n) :=
by simp only [add_zero, mul_one]