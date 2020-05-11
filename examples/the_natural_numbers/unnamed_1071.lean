import data.nat.basic

local postfix !:90 := nat.fact

-- BEGIN
example : 0! = 1 :=
by rw [nat.fact]

example (n : ℕ) : (n+1)! = (n+1) * n! :=
by rw [nat.fact]
-- END