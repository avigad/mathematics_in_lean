import algebra.big_operators

open finset
open_locale big_operators

local postfix !:90 := nat.fact

-- BEGIN
example (n : ℕ) : 1 ≤ n! :=
begin
  induction n with n ih,
  { rw [nat.fact] },
  rw nat.fact,
  show 0 < (n + 1) * n!,
  apply mul_pos,
  apply nat.succ_pos,
  apply ih
end
-- END