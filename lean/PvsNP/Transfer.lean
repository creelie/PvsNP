/-
(f) Arithmetic of the Transfer theorem.
-/
import Mathlib

namespace PvsNP

/-- With `0 < η < 1/(12 A₁)` the exponent `3 A₁ η` is below `1/4`. -/
theorem transfer_exponent (A₁ η : ℝ) (hA : 0 < A₁) (_hη : 0 < η) (h : η < 1 / (12 * A₁)) :
    3 * A₁ * η < 1 / 4 := by
  have h12 : (0 : ℝ) < 12 * A₁ := by positivity
  rw [lt_div_iff₀ h12] at h
  linarith

/-- Membership of the test circuit: if `0 < δ₁ < δ₂ < 1`, `d ≥ 1` and
`n ≥ d^{(1-δ₂)/(δ₂-δ₁)}`, then `(dn)^{1-δ₂} ≤ n^{1-δ₁}`. -/
theorem transfer_membership (d n δ₁ δ₂ : ℝ) (hd : 1 ≤ d) (hn : 0 < n)
    (h1 : 0 < δ₁) (h12 : δ₁ < δ₂) (h2 : δ₂ < 1)
    (hthr : d ^ ((1 - δ₂) / (δ₂ - δ₁)) ≤ n) :
    (d * n) ^ (1 - δ₂) ≤ n ^ (1 - δ₁) := by
  have hd0 : 0 < d := by linarith
  have hgap : 0 < δ₂ - δ₁ := by linarith
  -- d^{1-δ₂} ≤ n^{δ₂-δ₁}
  have key : d ^ (1 - δ₂) ≤ n ^ (δ₂ - δ₁) := by
    have := Real.rpow_le_rpow (by positivity) hthr hgap.le
    rw [← Real.rpow_mul hd0.le, div_mul_cancel₀ _ hgap.ne'] at this
    exact this
  rw [Real.mul_rpow hd0.le hn.le]
  calc d ^ (1 - δ₂) * n ^ (1 - δ₂) ≤ n ^ (δ₂ - δ₁) * n ^ (1 - δ₂) := by
        apply mul_le_mul_of_nonneg_right key (by positivity)
    _ = n ^ (1 - δ₁) := by rw [← Real.rpow_add hn]; ring_nf

end PvsNP
