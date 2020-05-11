import algebra.big_operators

open finset
open_locale big_operators

local postfix !:90 := nat.fact

-- BEGIN
example (n : ℕ) : n! = ∏ i in range n, (i + 1) :=
sorry
-- END