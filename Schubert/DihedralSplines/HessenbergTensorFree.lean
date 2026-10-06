import Schubert.DihedralSplines.SplineTensorFree
import Schubert.DihedralSplines.FlowupBasis

/-! # Graded equivariant freeness of geometric Hessenberg splines -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The Hessenberg spline action is its graded polynomial scalar extension. -/
theorem tensor_free :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod (polynomialRepresentation n)
          (RootSubset.Left.representation ideal.toRootSubset hthree))
        (ideal.toRootSubset.splineRepresentation hthree),
      (∀ degree, (Schubert.FiniteGroupCharacters.tensorPiece (P := Fin 2)
        (RootSubset.Left.piece ideal.toRootSubset hthree) degree).map equivalence.toLinearMap =
        ideal.toRootSubset.piece degree) ∧
      (∀ value : RootSubset.Left.Quotient ideal.toRootSubset hthree,
        RootSubset.Left.quotientMap ideal.toRootSubset hthree
          (equivalence (1 ⊗ₜ[ℂ] value)) = value) := by
  let := ideal.toRootSubset.leftAlgebra hthree
  exact RootSubset.Left.tensor_free ideal.toRootSubset hthree (FlowupSpline.Left.basis ideal)
    ideal.toRootSubset.length (fun vertex => by
      rw [FlowupSpline.Left.basis_apply]
      exact FlowupSpline.homogeneous ideal vertex)

end Left

namespace Right

/-- The Hessenberg spline action is its graded polynomial scalar extension. -/
theorem tensor_free :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
          (RootSubset.Right.representation ideal.toRootSubset hthree))
        (ideal.toRootSubset.splineRepresentation hthree),
      (∀ degree, (Schubert.FiniteGroupCharacters.tensorPiece (P := Fin 2)
        (RootSubset.Right.piece ideal.toRootSubset hthree) degree).map equivalence.toLinearMap =
        ideal.toRootSubset.piece degree) ∧
      (∀ value : RootSubset.Right.Quotient ideal.toRootSubset hthree,
        RootSubset.Right.quotientMap ideal.toRootSubset hthree
          (equivalence (1 ⊗ₜ[ℂ] value)) = value) := by
  let := ideal.toRootSubset.rightAlgebra hthree
  exact RootSubset.Right.tensor_free ideal.toRootSubset hthree (FlowupSpline.Right.basis ideal)
    ideal.toRootSubset.length (fun vertex => by
      rw [FlowupSpline.Right.basis_apply]
      exact FlowupSpline.homogeneous ideal vertex)

end Right

end Schubert.DihedralSplines.HessenbergIdeal
