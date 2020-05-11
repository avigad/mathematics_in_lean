import algebra.big_operators
import data.real.basic

open finset
open_locale big_operators

-- BEGIN
variables {R : Type*} [comm_ring R] (n : ℕ) (r : R)

example : (r - 1) * (∑ i in range n, r^i) = r^n - 1 :=
sorry
-- END