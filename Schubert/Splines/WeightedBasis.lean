import Schubert.Splines.WeightedMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Lifting finite bases through degree-decreasing changes -/

noncomputable section

namespace Schubert.Splines

/-- A basis change equal to the identity on nondecreasing weights gives another basis. -/
theorem weighted_basis_lift {R I M : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module R M] (basis : Module.Basis I R M) (weights : I → ℕ)
    (transform : M →ₗ[R] M)
    (hcoordinates : ∀ first second, weights second ≤ weights first →
      basis.repr (transform (basis second)) first = if first = second then 1 else 0)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    ∃ lifted : Module.Basis I R M, ∀ index, lifted index = transform (basis index) := by
  let matrix := LinearMap.toMatrixAlgEquiv basis transform
  have hdecrease : ∀ first second, weights second ≤ weights first →
      (matrix - 1) first second = 0 := by
    intro first second hweight
    change (LinearMap.toMatrixAlgEquiv basis transform) first second -
      (1 : Matrix I I R) first second = 0
    rw [LinearMap.toMatrixAlgEquiv_apply, Matrix.one_apply,
      hcoordinates first second hweight, sub_self]
  have hmatrix : IsUnit matrix := by
    have hunit := weighted_matrix_unit weights (matrix - 1) hdecrease bound hbound
    convert hunit using 1
    abel
  have htransform : IsUnit transform := by
    simpa only [matrix, AlgEquiv.symm_apply_apply] using
      hmatrix.map (LinearMap.toMatrixAlgEquiv basis).symm
  obtain ⟨unit, hunit⟩ := htransform
  refine ⟨basis.map (LinearMap.GeneralLinearGroup.toLinearEquiv unit), ?_⟩
  intro index
  rw [Module.Basis.map_apply]
  change (unit : M →ₗ[R] M) (basis index) = transform (basis index)
  rw [hunit]

end Schubert.Splines
