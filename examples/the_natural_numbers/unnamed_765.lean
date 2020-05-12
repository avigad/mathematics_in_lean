variables m n k : ℕ

-- BEGIN
example (h : m * n = k) (h' : n > 0) : m = k / n :=
begin
  symmetry,
  apply nat.div_eq_of_eq_mul_left h' h.symm,
end
-- END