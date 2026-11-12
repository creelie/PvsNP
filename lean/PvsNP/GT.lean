/-
(d) The greater-than matrix `GT_n` (rows and columns indexed by the `2^n` numbers of `n` bits,
entry `[x ≥ y]`) is lower triangular with ones on the diagonal, so its determinant is one
and its rank is `2^n`.
-/
import Mathlib

namespace PvsNP

/-- The matrix `[x ≥ y]` on a finite linear order, over a commutative ring `R`. -/
def GTMatrix (R : Type*) [CommRing R] (α : Type*) [LinearOrder α] : Matrix α α R :=
  Matrix.of fun x y => if y ≤ x then 1 else 0

theorem GTMatrix_det (R : Type*) [CommRing R] (α : Type*) [LinearOrder α] [Fintype α] :
    (GTMatrix R α).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [GTMatrix]
  · intro i j h
    have h' : i < j := h
    simp [GTMatrix, not_le.mpr h']

/-- `GT_n` over the integers. -/
abbrev GT (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ := GTMatrix ℤ (Fin (2 ^ n))

theorem GT_det (n : ℕ) : (GT n).det = 1 := GTMatrix_det ℤ _

theorem GT_det_ne_zero (n : ℕ) : (GT n).det ≠ 0 := by
  rw [GT_det]; exact one_ne_zero

/-- `GT_n` has full rank `2^n` over the rationals. -/
theorem GT_rank (n : ℕ) : (GTMatrix ℚ (Fin (2 ^ n))).rank = 2 ^ n := by
  have h : IsUnit (GTMatrix ℚ (Fin (2 ^ n))) := by
    rw [Matrix.isUnit_iff_isUnit_det, GTMatrix_det]
    exact isUnit_one
  rw [Matrix.rank_of_isUnit _ h]
  simp

/-- The same over any field. -/
theorem GTMatrix_rank (F : Type*) [Field F] (n : ℕ) :
    (GTMatrix F (Fin (2 ^ n))).rank = 2 ^ n := by
  have h : IsUnit (GTMatrix F (Fin (2 ^ n))) := by
    rw [Matrix.isUnit_iff_isUnit_det, GTMatrix_det]
    exact isUnit_one
  rw [Matrix.rank_of_isUnit _ h]
  simp

end PvsNP
