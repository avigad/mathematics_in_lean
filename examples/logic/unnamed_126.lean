import data.real.basic

-- BEGIN
lemma my_lemma : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  suffices h : abs x * abs y < 1 * ε,
  { rw [←abs_mul, one_mul] at h,
    apply h },
  calc
    abs x * abs y ≤ abs x * ε : sorry
    ... < 1 * ε               : sorry
end
-- END