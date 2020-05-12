open nat

variables m n : ℕ

-- BEGIN
example (h : succ m = succ n) : m = n :=
begin
  show pred (succ m) = pred (succ n),
  rw h
end
-- END