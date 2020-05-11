example (a b c d e f : ℕ) : a + b + (c + d) + (e + f) =
  f + (d + (c + b)) + e + a :=
by simp [add_assoc, add_comm, add_left_comm]

example (a b c d e f : ℕ) : min (min (min a b) (min c d)) (min e f) =
  min (min (min f (min d (min c b))) e) a :=
by simp [min_assoc, min_comm, min_left_comm]