import data.real.basic tactic

variables a b : ℝ

-- BEGIN
example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
sorry

#check abs_le'.mpr
-- END