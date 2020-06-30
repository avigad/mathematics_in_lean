import data.nat.sqrt

open nat

example (n : ℕ) : (sqrt n)^2 ≤ n :=
by { rw nat.pow_two, exact nat.sqrt_le n }

example (n : ℕ) : n < (sqrt n + 1)^2 :=
by { rw nat.pow_two, exact nat.lt_succ_sqrt n }