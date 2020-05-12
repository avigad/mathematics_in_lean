import algebra.big_operators

open finset

#eval finset.sum (range 5) (λ x, x^2)
#eval finset.sum (Ico 3 7) (λ x, x^2)