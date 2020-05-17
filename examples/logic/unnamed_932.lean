import data.real.basic

-- BEGIN
example (a b : ℝ) : abs a = abs (a + b - b) :=
by  { congr, ring }
-- END