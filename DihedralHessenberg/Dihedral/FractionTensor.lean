import DihedralHessenberg.Dihedral.FractionGalois
import DihedralHessenberg.Splines.GaloisTensor

/-! # Tensor splitting over the invariant fraction field -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral

attribute [local instance] FractionRing.liftAlgebra

/-- The canonical tensor splitting of the invariant fraction-field extension. -/
def fractionTensorEquiv (n : ℕ) [NeZero n] :
    FractionRing CoordinatePolynomial ⊗[FractionRing (invariantSubalgebra n)]
      FractionRing CoordinatePolynomial ≃ₐ[FractionRing CoordinatePolynomial]
      (DihedralGroup n → FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  let := fraction_isGaloisGroup n
  exact Splines.galoisTensorEquiv (DihedralGroup n)
    (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial)

/-- The tensor splitting sends each pure tensor to its action-product function. -/
theorem fractionTensorEquiv_tmul (n : ℕ) [NeZero n]
    (first second : FractionRing CoordinatePolynomial) (element : DihedralGroup n) :
    letI := fractionMulAction n
    fractionTensorEquiv n (first ⊗ₜ[FractionRing (invariantSubalgebra n)] second) element =
      first * element • second := rfl

end Schubert.Dihedral
