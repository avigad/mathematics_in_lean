import data.real.basic

-- BEGIN
def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → abs (s n - a) < ε
-- END