import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction

theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
      specialize ih (m + 1)
      rw [add_assoc m 1 n, add_comm 1 n] at ih
      simp only [fib_add_two, Nat.succ_eq_add_one, ih]
      ring

example (n : ℕ): (fib n)^2 + (fib (n + 1))^2 = fib (2 * n + 1) :=
  sorry

