import Mathlib

/-!
# Classical real inequalities
-/

namespace LeanProofs

/-- Bernoulli's inequality for `x ≥ 0`. -/
theorem bernoulli (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (1 + k * x) * (1 + x) ≤ (1 + x) ^ k * (1 + x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (k : ℝ) * x * x :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hx) hx
    rw [pow_succ]
    push_cast
    nlinarith [h1, h2]

/-- AM-GM for two nonnegative reals. -/
theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
  nlinarith [sq_nonneg (a - b)]

/-- Cauchy–Schwarz in dimension two. -/
theorem cauchy_schwarz_two (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

end LeanProofs
