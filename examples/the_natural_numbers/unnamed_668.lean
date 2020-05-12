import data.real.basic

local attribute [simp] abs_of_nonneg

example (a : ℝ) (f : ℝ → ℝ) (h: a ≥ 0) : f (abs a) = f a :=
by simp *