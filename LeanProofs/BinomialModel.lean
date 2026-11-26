import Mathlib

/-!
# One-period binomial model (Cox–Ross–Rubinstein)

A market with one stock and one riskless bond over a single period.
The stock is worth `S₀` today and `S₀ * u` (up) or `S₀ * d` (down) tomorrow;
the bond is worth `1` today and `R` tomorrow.

Main results:

* `BinomialModel.noArbitrage_iff` : the market admits no arbitrage iff `d < R < u`;
* `BinomialModel.noArbitrage_iff_riskNeutralProb` : equivalently, the risk-neutral
  probability `q = (R - d) / (u - d)` lies strictly between `0` and `1`;
* `BinomialModel.replication` : every contingent claim `(Xu, Xd)` can be replicated by a
  portfolio of stock and bond, whose initial value is the risk-neutral price
  `(q * Xu + (1 - q) * Xd) / R`.
-/

namespace LeanProofs

/-- A one-period binomial market. -/
structure BinomialModel where
  /-- Initial stock price. -/
  S₀ : ℝ
  /-- Up factor. -/
  u : ℝ
  /-- Down factor. -/
  d : ℝ
  /-- Gross riskless return `1 + r`. -/
  R : ℝ
  S₀_pos : 0 < S₀
  d_pos : 0 < d
  d_lt_u : d < u
  R_pos : 0 < R

namespace BinomialModel

variable (M : BinomialModel)

/-- Gain at maturity, in the up state, of `θ` shares financed at the riskless rate. -/
def gainUp (θ : ℝ) : ℝ := θ * M.S₀ * (M.u - M.R)

/-- Gain at maturity, in the down state, of `θ` shares financed at the riskless rate. -/
def gainDown (θ : ℝ) : ℝ := θ * M.S₀ * (M.d - M.R)

/-- An arbitrage: a zero-cost strategy that never loses and wins in some state. -/
def IsArbitrage (θ : ℝ) : Prop :=
  0 ≤ M.gainUp θ ∧ 0 ≤ M.gainDown θ ∧ (0 < M.gainUp θ ∨ 0 < M.gainDown θ)

/-- The market has no arbitrage. -/
def NoArbitrage : Prop := ∀ θ, ¬ M.IsArbitrage θ

/-- The risk-neutral probability of the up state. -/
noncomputable def riskNeutralProb : ℝ := (M.R - M.d) / (M.u - M.d)

/-- No arbitrage holds iff `d < R < u`. -/
theorem noArbitrage_iff : M.NoArbitrage ↔ M.d < M.R ∧ M.R < M.u := by
  have hS := M.S₀_pos
  have hdu := M.d_lt_u
  unfold NoArbitrage
  constructor
  · intro h
    by_contra hcon
    simp only [not_and_or, not_lt] at hcon
    rcases hcon with hRd | huR
    · have hu : 0 < M.u - M.R := by linarith
      have hd' : 0 ≤ M.d - M.R := by linarith
      apply h 1
      unfold IsArbitrage
      refine ⟨?_, ?_, Or.inl ?_⟩
      · simp only [gainUp]; nlinarith [mul_pos hS hu]
      · simp only [gainDown]; nlinarith [mul_nonneg hS.le hd']
      · simp only [gainUp]; nlinarith [mul_pos hS hu]
    · have hR : 0 < M.R - M.d := by linarith
      apply h (-1)
      unfold IsArbitrage
      refine ⟨?_, ?_, Or.inr ?_⟩
      · simp only [gainUp]; nlinarith [mul_nonneg hS.le (sub_nonneg.2 huR)]
      · simp only [gainDown]; nlinarith [mul_pos hS hR]
      · simp only [gainDown]; nlinarith [mul_pos hS hR]
  · rintro ⟨hdR, hRu⟩ θ hθ
    unfold IsArbitrage gainUp gainDown at hθ
    obtain ⟨h1, h2, h3⟩ := hθ
    have hA : 0 < M.S₀ * (M.u - M.R) := mul_pos hS (by linarith)
    have hB : 0 < M.S₀ * (M.R - M.d) := mul_pos hS (by linarith)
    have hθ1 : 0 ≤ θ := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_neg_of_neg_of_pos hneg hA]
    have hθ2 : θ ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      nlinarith [mul_pos hpos hB]
    have hθ0 : θ = 0 := le_antisymm hθ2 hθ1
    subst hθ0
    simp at h3

/-- No arbitrage holds iff the risk-neutral probability is strictly between `0` and `1`. -/
theorem noArbitrage_iff_riskNeutralProb :
    M.NoArbitrage ↔ 0 < M.riskNeutralProb ∧ M.riskNeutralProb < 1 := by
  have hpos : 0 < M.u - M.d := sub_pos.2 M.d_lt_u
  rw [noArbitrage_iff]
  unfold riskNeutralProb
  rw [div_pos_iff_of_pos_right hpos, div_lt_one hpos]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Every claim paying `Xu` (up) or `Xd` (down) is replicated by `θ` shares and `β` bonds,
and the initial value of the replicating portfolio is the risk-neutral price. -/
theorem replication (Xu Xd : ℝ) :
    ∃ θ β : ℝ, θ * (M.S₀ * M.u) + β * M.R = Xu ∧
      θ * (M.S₀ * M.d) + β * M.R = Xd ∧
      θ * M.S₀ + β = (M.riskNeutralProb * Xu + (1 - M.riskNeutralProb) * Xd) / M.R := by
  have hS : M.S₀ ≠ 0 := M.S₀_pos.ne'
  have hR : M.R ≠ 0 := M.R_pos.ne'
  have hud : M.u - M.d ≠ 0 := (sub_pos.2 M.d_lt_u).ne'
  refine ⟨(Xu - Xd) / (M.S₀ * (M.u - M.d)),
    (M.u * Xd - M.d * Xu) / ((M.u - M.d) * M.R), ?_, ?_, ?_⟩
  · field_simp
    try ring
  · field_simp
    try ring
  · unfold riskNeutralProb
    field_simp
    try ring

end BinomialModel

end LeanProofs
