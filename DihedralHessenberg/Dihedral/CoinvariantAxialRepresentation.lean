import DihedralHessenberg.Dihedral.CoinvariantAction
import DihedralHessenberg.Dihedral.CoinvariantAxialAction
import DihedralHessenberg.Dihedral.FrequencyEigenbasis

/-! # Operators on coinvariant axial vectors

Rotations are diagonal on the axial power classes; the first simple reflection
interchanges them with the parity sign of their polynomial degree.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every rotation acts diagonally on the class of a power of u. -/
theorem _root_.Schubert.Dihedral.Coinvariant.r_u_pow (n : ℕ) [NeZero n]
    (exponent : ZMod n) (degree : ℕ) :
    coinvariantRepresentation n (.r exponent)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree)) =
      ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ exponent.val) ^ degree •
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree) := by
  rw [coinvariantRepresentation_mk]
  have hpoly : polynomialAction n (.r exponent) (auxiliaryU ^ degree) =
      ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ exponent.val) ^ degree •
        (auxiliaryU ^ degree) := by
    rw [map_pow, polynomialAction_r_auxiliaryU_pow, mul_pow, ← map_pow]
    rw [MvPolynomial.smul_eq_C_mul]
  rw [hpoly]
  exact (Ideal.Quotient.mkₐ ℂ (coinvariantIdeal n)).toLinearMap.map_smul _ _

/-- Every rotation acts diagonally on the class of a power of v. -/
theorem _root_.Schubert.Dihedral.Coinvariant.r_v_pow (n : ℕ) [NeZero n]
    (exponent : ZMod n) (degree : ℕ) :
    coinvariantRepresentation n (.r exponent)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)) =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent.val) ^ degree •
        Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree) := by
  rw [coinvariantRepresentation_mk]
  have hpoly : polynomialAction n (.r exponent) (auxiliaryV ^ degree) =
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent.val) ^ degree •
        (auxiliaryV ^ degree) := by
    rw [map_pow, polynomialAction_r_auxiliaryV_pow, mul_pow, ← map_pow]
    rw [MvPolynomial.smul_eq_C_mul]
  rw [hpoly]
  exact (Ideal.Quotient.mkₐ ℂ (coinvariantIdeal n)).toLinearMap.map_smul _ _

/-- The first simple reflection sends the u power class to the signed v power class. -/
theorem _root_.Schubert.Dihedral.Coinvariant.s1_u_pow (n : ℕ) [NeZero n] (degree : ℕ) :
    coinvariantRepresentation n (firstSimpleReflection n)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree)) =
      ((-1 : ℂ) ^ degree) • Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree) := by
  rw [coinvariantRepresentation_mk, coinvariant_firstSimple_auxiliaryU_pow]
  simpa only [map_pow, map_neg, map_one] using
    (Algebra.smul_def ((-1 : ℂ) ^ degree)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree))).symm

/-- The first simple reflection sends the v power class to the signed u power class. -/
theorem _root_.Schubert.Dihedral.Coinvariant.s1_v_pow (n : ℕ) [NeZero n] (degree : ℕ) :
    coinvariantRepresentation n (firstSimpleReflection n)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ degree)) =
      ((-1 : ℂ) ^ degree) • Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree) := by
  rw [coinvariantRepresentation_mk, coinvariant_firstSimple_auxiliaryV_pow]
  simpa only [map_pow, map_neg, map_one] using
    (Algebra.smul_def ((-1 : ℂ) ^ degree)
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ degree))).symm

end Schubert.Dihedral
