import DihedralHessenberg.Paper.SplinePieceSection

/-! # Scalar compatibility of the geometric dot representation -/

noncomputable section
namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Dot translation acts on constant polynomial coefficients by substitution. -/
theorem left_smul_dot (element : DihedralGroup n) (polynomial : CoordinatePolynomial)
    (value : selected.Spline) :
    letI := selected.leftAlgebra hthree
    selected.splineRepresentation hthree element (polynomial • value) =
      polynomialAction n element polynomial •
        selected.splineRepresentation hthree element value := by
  let := selected.leftAlgebra hthree
  apply Subtype.ext
  funext vertex
  change polynomialAction n element (polynomial * value.val (element⁻¹ * vertex)) =
    polynomialAction n element polynomial *
      polynomialAction n element (value.val (element⁻¹ * vertex))
  exact map_mul _ _ _

/-- Dot translation fixes orbit polynomial coefficients. -/
theorem right_smul_dot (element : DihedralGroup n) (polynomial : CoordinatePolynomial)
    (value : selected.Spline) :
    letI := selected.rightAlgebra hthree
    selected.splineRepresentation hthree element (polynomial • value) =
      polynomial • selected.splineRepresentation hthree element value := by
  let := selected.rightAlgebra hthree
  apply Subtype.ext
  funext vertex
  change polynomialAction n element
    (polynomialAction n (element⁻¹ * vertex) polynomial * value.val (element⁻¹ * vertex)) =
      polynomialAction n vertex polynomial *
        polynomialAction n element (value.val (element⁻¹ * vertex))
  rw [map_mul]
  have hcompose : polynomialAction n element
      (polynomialAction n (element⁻¹ * vertex) polynomial) =
      polynomialAction n vertex polynomial := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  rw [hcompose]

end Schubert.Dihedral.RootSubset
