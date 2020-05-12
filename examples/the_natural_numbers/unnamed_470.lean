namespace my_nat

-- BEGIN
def fact : ℕ → ℕ
| 0     := 1
| (n+1) := (n+1) * fact n

theorem fact_pos (n : ℕ) : 0 < fact n :=
begin
  induction n with n ih,
  { apply zero_lt_one },
  exact mul_pos (nat.succ_pos _) ih
end

#eval fact 100
-- END

end my_nat