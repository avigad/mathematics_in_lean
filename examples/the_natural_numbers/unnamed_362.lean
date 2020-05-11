namespace my_nat

-- BEGIN
def pred : ℕ → ℕ
| 0     := 0
| (n+1) := n

def sub (m : ℕ) : ℕ → ℕ
| 0     := m
| (n+1) := pred (sub n)
-- END

end my_nat