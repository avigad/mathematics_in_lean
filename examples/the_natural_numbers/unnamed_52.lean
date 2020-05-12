open nat

namespace my_nat

def add : ℕ → ℕ → ℕ
| m 0        := m
| m (succ n) := succ (add m n)

end my_nat