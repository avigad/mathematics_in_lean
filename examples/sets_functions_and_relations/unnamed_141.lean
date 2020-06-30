def gaussian_integer := ℤ × ℤ

notation `ℤ[i]` := gaussian_integer

namespace gaussian_integer

def zero : ℤ[i] := ⟨0, 0⟩
def one : ℤ[i]  := ⟨1, 0⟩
def ii : ℤ[i]   := ⟨0, 1⟩

def add : ℤ[i] → ℤ[i] → ℤ[i] := λ ⟨a, b⟩ ⟨c, d⟩, ⟨a + c, b + d⟩
def mul : ℤ[i] → ℤ[i] → ℤ[i] := λ ⟨a, b⟩ ⟨c, d⟩, ⟨a*c - b*d, a*d + b*c⟩
def neg : ℤ[i] → ℤ[i]        := λ ⟨a, b⟩, ⟨-a, -b⟩

instance : has_zero ℤ[i] := ⟨zero⟩
instance : has_one  ℤ[i] := ⟨one⟩
instance : has_add  ℤ[i] := ⟨add⟩
instance : has_mul  ℤ[i] := ⟨mul⟩
instance : has_neg  ℤ[i] := ⟨neg⟩

end gaussian_integer

-- BEGIN
open gaussian_integer

variables z w : ℤ[i]

#check (12345 : ℤ[i])
#check z + 12345
#check (z + 1) * -w

theorem ii_mul_ii : ii * ii = -1 := rfl
-- END