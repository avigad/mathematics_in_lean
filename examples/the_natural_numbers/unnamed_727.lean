variables m n : ℕ

-- BEGIN
example (h : m < n) : m + 1 ≤ n := h

example (h : 0 < n) : 1 ≤ n := h
-- END