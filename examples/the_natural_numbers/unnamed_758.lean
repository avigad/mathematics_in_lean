import data.nat.basic

variables m n k : ℕ

-- BEGIN
example (h : m = k + n) : m - n = k :=
by rw [h, nat.add_sub_cancel]
-- END