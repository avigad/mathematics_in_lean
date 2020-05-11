open nat

namespace my_nat

-- BEGIN
def pow (b : ℕ) : ℕ → ℕ
| 0        := 1
| (succ n) := pow n * b
-- END

end my_nat