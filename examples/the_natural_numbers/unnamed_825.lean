import data.finset

open finset

#eval range 5
#eval Ico 3 7

example : range 5 = {0, 1, 2, 3, 4} :=
dec_trivial

example : range 5 = {4, 1, 2, 0, 0, 3} :=
dec_trivial

example : Ico 3 7 = {3, 4, 5, 6} :=
dec_trivial

example : Ico 3 7 = {6, 3, 3, 5, 4} :=
dec_trivial