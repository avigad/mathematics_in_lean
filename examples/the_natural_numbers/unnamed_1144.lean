import algebra.big_operators

open finset
open_locale big_operators

local postfix !:90 := nat.fact

-- BEGIN
example (n i : ℕ) (h : i ≠ 0) (h' : i ≤ n) : i ∣ n! :=
begin
induction n with n ih,
{ intros, simp at h', contradiction  },
cases h' with _ h',
{ apply dvd_mul_right },
apply dvd_mul_of_dvd_right,
apply ih h',
end
-- END