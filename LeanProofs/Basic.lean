import Mathlib

/-!
# Elementary summation identities

Classical closed forms for finite sums over `ℕ`, proved by induction.
-/

open Finset

namespace LeanProofs

/-- Gauss: twice the sum of `0, …, n` is `n * (n + 1)`. -/
theorem gauss_sum (n : ℕ) : (∑ i ∈ range (n + 1), i) * 2 = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    nlinarith [ih]

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    ring

/-- Sum of squares: `6 * ∑_{i ≤ n} i ^ 2 = n (n + 1) (2 n + 1)`. -/
theorem sum_sq (n : ℕ) :
    6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    nlinarith [ih]

end LeanProofs
