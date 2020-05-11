variable n : ℕ

-- BEGIN
example (h : n ≠ 0) : 0 < n :=
nat.pos_of_ne_zero h

example (h : 0 < n) : n ≠ 0 :=
ne_of_gt h
-- END