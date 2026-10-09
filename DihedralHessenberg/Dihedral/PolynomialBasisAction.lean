import DihedralHessenberg.Dihedral.PolynomialPieceRepresentation
import DihedralHessenberg.Dihedral.AuxiliaryHomogeneous
import DihedralHessenberg.Dihedral.InvariantsBasic
import Mathlib.LinearAlgebra.Trace

/-! # Rotation eigenvalues of the homogeneous polynomial basis -/

noncomputable section
namespace Schubert.Dihedral

/-- The auxiliary basis vector is its two-coordinate monomial. -/
theorem auxiliaryPieceBasis_product (degree : ℕ)
    (exponent : {exponent : Fin 2 →₀ ℕ // exponent.degree = degree}) :
    (auxiliaryPieceBasis degree exponent).val =
      auxiliaryU ^ exponent.val 0 * auxiliaryV ^ exponent.val 1 := by
  rw [auxiliaryPieceBasis_apply, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_mul, map_one, one_mul, map_pow, Fin.prod_univ_two]
  simp [auxiliaryCoordinateHom]

/-- Rotation diagonalizes the polynomial degree basis in the auxiliary coordinates. -/
theorem polynomialPiece_r_basis (n : ℕ) [NeZero n] (degree : ℕ) (coordinate : ZMod n)
    (exponent : {exponent : Fin 2 →₀ ℕ // exponent.degree = degree}) :
    polynomialPieceRepresentation n degree (.r coordinate) (auxiliaryPieceBasis degree exponent) =
      (Complex.exp (((-(2 * Real.pi * coordinate.val / n) : ℝ) : ℂ) * Complex.I) ^
          exponent.val 0 *
        Complex.exp (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) ^
          exponent.val 1) • auxiliaryPieceBasis degree exponent := by
  apply Subtype.ext
  change polynomialAction n (.r coordinate) (auxiliaryPieceBasis degree exponent).val =
    (Complex.exp (((-(2 * Real.pi * coordinate.val / n) : ℝ) : ℂ) * Complex.I) ^
        exponent.val 0 *
      Complex.exp (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) ^
        exponent.val 1) • (auxiliaryPieceBasis degree exponent).val
  rw [auxiliaryPieceBasis_product]
  rw [map_mul, map_pow, map_pow, polynomialAction_r_auxiliaryU,
    polynomialAction_r_auxiliaryV]
  simp only [mul_pow, Algebra.smul_def]
  change _ = MvPolynomial.C _ * _
  rw [map_mul, map_pow, map_pow]
  ring

/-- The polynomial degree rotation character is the sum of its monomial eigenvalues. -/
theorem polynomialPiece_character_r (n : ℕ) [NeZero n] (degree : ℕ) (coordinate : ZMod n) :
    let := FiniteDimensional.fintypeBasisIndex (auxiliaryPieceBasis degree)
    (polynomialPieceFDRep n degree).character (.r coordinate) =
      ∑ exponent : {exponent : Fin 2 →₀ ℕ // exponent.degree = degree},
        Complex.exp (((-(2 * Real.pi * coordinate.val / n) : ℝ) : ℂ) * Complex.I) ^
            exponent.val 0 *
          Complex.exp (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) ^
            exponent.val 1 := by
  classical
  let := FiniteDimensional.fintypeBasisIndex (auxiliaryPieceBasis degree)
  change LinearMap.trace ℂ _ (polynomialPieceRepresentation n degree (.r coordinate)) = _
  rw [LinearMap.trace_eq_matrix_trace ℂ (auxiliaryPieceBasis degree)]
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro exponent _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, polynomialPiece_r_basis]
  simp

end Schubert.Dihedral
