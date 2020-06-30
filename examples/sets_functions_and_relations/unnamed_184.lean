def gaussian_integer := ℤ × ℤ

notation `ℤ[i]` := gaussian_integer

namespace gaussian_integer

-- BEGIN
def add : ℤ[i] → ℤ[i] → ℤ[i]
| (a, b) (c, d) := (a + c, b + d)

def mul : ℤ[i] → ℤ[i] → ℤ[i]
| (a, b) (c, d) := (a*c - b*d, a*d + b*c)

def neg : ℤ[i] → ℤ[i]
| (a, b) := (-a, -b)
-- END

end gaussian_integer