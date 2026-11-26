import Mathlib

/-!
# `n`-period binomial tree (Cox–Ross–Rubinstein pricing)

On a recombining binomial tree with `n` steps, a contingent claim is described by its payoff
`g k` as a function of the number `k` of "up" moves.  Its price is computed by backward induction
under the risk-neutral probability `q` of an up move, discounting by the one-period gross return
`R` at each step.

Main results:

* `crrValue_eq` : the backward-induction value equals the closed form
  `(∑_{k} C(n,k) qᵏ (1-q)ⁿ⁻ᵏ g k) / Rⁿ` (the CRR formula);
* `crrValue_const` : a riskless payoff `c` is worth `c / Rⁿ`;
* `crrValue_nonneg` : prices of nonnegative claims are nonnegative;
* `callPrice_eq` : the European call formula.
-/

open Finset

namespace LeanProofs

/-- Backward-induction value of a claim with payoff `g k` after `k` up moves, on an `n`-step
tree with risk-neutral up probability `q` and one-period gross return `R`. -/
noncomputable def crrValue (q R : ℝ) : ℕ → (ℕ → ℝ) → ℝ
  | 0, g => g 0
  | n + 1, g => (q * crrValue q R n (fun k => g (k + 1)) + (1 - q) * crrValue q R n g) / R

/-- One step: this is the one-period pricing formula. -/
theorem crrValue_one (q R : ℝ) (g : ℕ → ℝ) :
    crrValue q R 1 g = (q * g 1 + (1 - q) * g 0) / R := by
  simp [crrValue]

/-- A riskless payoff `c` is worth `c / Rⁿ`. -/
theorem crrValue_const (q R c : ℝ) (n : ℕ) : crrValue q R n (fun _ => c) = c / R ^ n := by
  induction n with
  | zero => simp [crrValue]
  | succ n ih =>
    simp only [crrValue, ih]
    ring

/-- Prices of nonnegative claims are nonnegative. -/
theorem crrValue_nonneg {q R : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hR : 0 < R) (n : ℕ)
    (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) : 0 ≤ crrValue q R n g := by
  induction n generalizing g with
  | zero => simpa [crrValue] using hg 0
  | succ n ih =>
    simp only [crrValue]
    refine div_nonneg (add_nonneg (mul_nonneg hq₀ (ih _ fun k => hg _))
      (mul_nonneg (by linarith) (ih g hg))) hR.le

/-- **CRR pricing formula.**  The backward-induction value equals the discounted risk-neutral
expectation of the payoff, written as a binomial sum over the antidiagonal
`{(i, j) | i + j = n}` (`i` up moves, `j` down moves). -/
theorem crrValue_eq (q R : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    crrValue q R n g =
      (∑ ij ∈ antidiagonal n,
        (n.choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ ij.2 * g ij.1)) / R ^ n := by
  induction n generalizing g with
  | zero => simp [crrValue]
  | succ n ih =>
    have key : (∑ ij ∈ antidiagonal (n + 1),
          ((n + 1).choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ ij.2 * g ij.1)) =
        (∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ (ij.2 + 1) * g ij.1)) +
        ∑ ij ∈ antidiagonal n,
          (n.choose ij.2 : ℝ) * (q ^ (ij.1 + 1) * (1 - q) ^ ij.2 * g (ij.1 + 1)) :=
      Finset.sum_antidiagonal_choose_succ_mul (fun i j => q ^ i * (1 - q) ^ j * g i) n
    have h1 : (∑ ij ∈ antidiagonal n,
          (n.choose ij.2 : ℝ) * (q ^ (ij.1 + 1) * (1 - q) ^ ij.2 * g (ij.1 + 1))) =
        q * ∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ ij.2 * g (ij.1 + 1)) := by
      rw [mul_sum]
      refine sum_congr rfl fun ij hij => ?_
      rw [← Nat.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]
      ring
    have h2 : (∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ (ij.2 + 1) * g ij.1)) =
        (1 - q) * ∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : ℝ) * (q ^ ij.1 * (1 - q) ^ ij.2 * g ij.1) := by
      rw [mul_sum]
      refine sum_congr rfl fun ij _ => ?_
      ring
    rw [crrValue, ih, ih, key, h1, h2]
    ring

/-- Payoff of a European call with strike `K` after `k` up moves out of `n`. -/
noncomputable def callPayoff (S₀ u d K : ℝ) (n k : ℕ) : ℝ :=
  max (S₀ * u ^ k * d ^ (n - k) - K) 0

/-- Price of a European call on the `n`-step tree. -/
noncomputable def callPrice (S₀ u d K q R : ℝ) (n : ℕ) : ℝ :=
  crrValue q R n (callPayoff S₀ u d K n)

/-- **European call formula** on the binomial tree. -/
theorem callPrice_eq (S₀ u d K q R : ℝ) (n : ℕ) :
    callPrice S₀ u d K q R n =
      (∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℝ) *
        (q ^ ij.1 * (1 - q) ^ ij.2 * max (S₀ * u ^ ij.1 * d ^ (n - ij.1) - K) 0)) / R ^ n :=
  crrValue_eq q R n (callPayoff S₀ u d K n)

/-- A call has nonnegative price whenever `q ∈ [0, 1]` and `R > 0`. -/
theorem callPrice_nonneg {q R : ℝ} (S₀ u d K : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hR : 0 < R)
    (n : ℕ) : 0 ≤ callPrice S₀ u d K q R n :=
  crrValue_nonneg hq₀ hq₁ hR n _ fun _ => le_max_right _ _

end LeanProofs
