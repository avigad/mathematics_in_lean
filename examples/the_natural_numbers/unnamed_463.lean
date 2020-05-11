def factorial : ℕ → ℕ
| 0     := 1
| (n+1) := (n+1) * factorial n

theorem factorial_pos (n : ℕ) : 0 < factorial n :=
begin
  induction n with n ih,
  { apply zero_lt_one },
  exact mul_pos (nat.succ_pos _) ih
end

#eval factorial 100