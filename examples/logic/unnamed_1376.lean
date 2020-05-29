variable a : ℕ

-- BEGIN
example (h : 0 < 0) : a > 12 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 12 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 12 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end
-- END