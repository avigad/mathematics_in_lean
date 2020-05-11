open nat

variables m n k : ℕ

namespace my_nat

-- BEGIN
theorem add_right_cancel (h : m + n = k + n) : m = k :=
begin
  induction n with n ih,
  { apply h },
  apply ih,
  apply succ.inj h
end
-- END

end my_nat