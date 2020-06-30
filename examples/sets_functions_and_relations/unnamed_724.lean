import tactic

variables x y : pnat

#check x.val
#check x.prop

example : pnat := subtype.mk 5 (by norm_num)

example : pnat := ⟨5, by norm_num⟩

example (h : x.val = y.val) : x = y :=
by { ext, apply h }