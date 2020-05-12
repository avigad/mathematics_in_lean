import algebra.big_operators

open finset
open_locale big_operators

variable n : ℕ

-- BEGIN
example : 2 * ∑ i in range (n + 1), i = n * (n + 1) :=
begin
  induction n with n ih,
  { rw [sum_range_succ, sum_range_zero],
    refl },
  rw [sum_range_succ, mul_add, ih],
  rw [nat.succ_eq_add_one],
  ring
end
-- END