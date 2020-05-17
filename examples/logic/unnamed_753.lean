import tactic

variables {α : Type*} [comm_ring α]

def sos (x : α) := ∃ a b, x = a^2 + b^2

theorem sos_mul {x y : α} (sosx : sos x) (sosy : sos y) : sos (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  use [a*c - b*d, a*d + b*c],
  rw [xeq, yeq], ring
end