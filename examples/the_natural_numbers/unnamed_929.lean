import algebra.big_operators

open finset
open_locale big_operators

variable n : ℕ

-- BEGIN
example : 2 * ∑ i in range (n + 1), i = n * (n + 1) :=
begin
  induction n with n ih,
  { simp },
  rw [sum_range_succ, mul_add, ih],
  simp only [nat.succ_eq_add_one],
  ring
end
-- END