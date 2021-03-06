import data.nat.parity tactic
open nat

-- BEGIN
example : ∀ m n : nat, even n → even (m * n) :=
by intros; simp * with parity_simps
-- END