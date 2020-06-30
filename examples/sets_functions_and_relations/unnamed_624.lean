import tactic.linarith
import data.nat.gcd

open function

def f (p : ℕ × ℕ) : ℕ := (p.1 + p.2)^2 + p.1

theorem aux {x y x' y' : ℕ} (h : (x + y)^2 + x ≤ (x' + y')^2 + x') :
  x + y ≤ x' + y' :=
begin
  contrapose! h,
  have h1 : x' + y' + 1 ≤ x + y := h,
  calc
    (x' + y')^2 + x' ≤ (x' + y')^2 + (x' + y') : by linarith
    ... = (x' + y' + 1) * (x' + y')            : by ring
    ... ≤ (x + y) * (x' + y')                  :
            mul_le_mul_of_nonneg_right h1 (zero_le _)
    ... < (x + y)^2                            :
            by { rw [nat.pow_two, mul_lt_mul_left],
                 exact h,
                 linarith }
    ... ≤ (x + y)^2 + x                        : by linarith
end

theorem inj_f : injective f :=
begin
  intros p q h,
  dsimp [f] at h,
  have : p.1 + p.2 = q.1 + q.2,
  { sorry },
  rw this at h,
  have : p.1 = q.1,
  { sorry },
  have : p.2 = q.2,
  { sorry },
  ext; assumption
end