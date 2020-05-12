import algebra.big_operators

open finset
open_locale big_operators

-- BEGIN
variables {α : Type*} [add_comm_monoid α]
variables (n : ℕ) (f : ℕ → α)

#check (sum_range_zero f : ∑ x in range 0, f x = 0)
#check (sum_range_succ f n :
  ∑ i in range (n + 1), f i = f n + (∑ i in range n, f i))
-- END