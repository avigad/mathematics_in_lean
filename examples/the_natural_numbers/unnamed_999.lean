import algebra.big_operators

open finset
open_locale big_operators

variable n : ℕ

-- BEGIN
example : 4 * ∑ i in range (n + 1), i^3 = n^2 * (n + 1)^2 :=
begin
  have pow_three : ∀ n : nat, n^3 = n * n * n,
  { intro n, simp [nat.pow_succ] },
  sorry
end
-- END