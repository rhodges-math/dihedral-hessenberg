import Schubert.Dihedral.FirstLocalization
import Schubert.Dihedral.InvariantTensorEvaluation

/-! # Compatibility of the polynomial tensor evaluation with fraction localization -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral

/-- The fraction splitting is the localization of the polynomial evaluation. -/
theorem tensorEvaluation_localized (n : ℕ) [NeZero n]
    (value : CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
    (element : DihedralGroup n) :
    fractionPolynomialEquiv n
      ((Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom (invariantSubalgebra n) CoordinatePolynomial
          (FractionRing CoordinatePolynomial)) (AlgHom.id (invariantSubalgebra n)
          CoordinatePolynomial)) value) element =
      algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial)
        (tensorEvaluation n value element) := by
  induction value using TensorProduct.inductionOn with
  | tmul first second =>
      rw [Algebra.TensorProduct.map_tmul, fractionPolynomialEquiv_tmul,
        tensorEvaluation_tmul, map_mul]
      rfl
  | add first second hfirst hsecond =>
      simp only [map_add, Pi.add_apply, hfirst, hsecond]

end Schubert.Dihedral
