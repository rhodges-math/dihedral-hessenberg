import Schubert.DihedralSplines.SplineTensorAugmentation
import Schubert.FiniteGroupCharacters.TensorAugmentationTransport

/-! # Exact homogeneous positive-scalar tensor images in coordinate ideals -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral.RootSubset
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n] {I : Type*} [Fintype I] [DecidableEq I]
variable (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

omit [NeZero n] in
/-- The complex-linear coordinate projection has its coordinate ideal kernel. -/
theorem map_kernel_linear :
    LinearMap.ker (quotientMap selected hthree).toLinearMap =
      (ideal selected hthree).restrictScalars ℂ := by
  ext value
  exact map_zero_iff selected hthree value

/-- Graded scalar extension identifies the entire positive tensor part with the coordinate ideal. -/
theorem tensor_positive_ideal (basis : letI := selected.leftAlgebra hthree
    Module.Basis I Schubert.Dihedral.CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod (Schubert.Dihedral.polynomialRepresentation n)
          (representation selected hthree))
        (selected.splineRepresentation hthree),
      (∀ degree, (tensorPiece (P := Fin 2) (piece selected hthree) degree).map
        equivalence.toLinearMap = selected.piece degree) ∧
      (positiveTensor (P := Fin 2)).map equivalence.toLinearMap =
        (ideal selected hthree).restrictScalars ℂ ∧
      (∀ degree, (positiveTensor ⊓ tensorPiece (P := Fin 2) (piece selected hthree) degree).map
        equivalence.toLinearMap =
          (ideal selected hthree).restrictScalars ℂ ⊓ selected.piece degree) := by
  let := selected.leftAlgebra hthree
  obtain ⟨equivalence, hdegrees, hpure⟩ := tensor_free_augmentation selected hthree
    basis weights hbasis
  have hkernel := positive_tensor_map (quotientBasis selected hthree basis)
    equivalence.toLinearEquiv (quotientMap selected hthree).toLinearMap hpure
  rw [map_kernel_linear] at hkernel
  refine ⟨equivalence, hdegrees, hkernel, ?_⟩
  intro degree
  rw [Submodule.map_inf _ equivalence.toLinearEquiv.injective, hkernel, hdegrees]

end Left

namespace Right

omit [NeZero n] in
/-- The complex-linear coordinate projection has its coordinate ideal kernel. -/
theorem map_kernel_linear :
    LinearMap.ker (quotientMap selected hthree).toLinearMap =
      (ideal selected hthree).restrictScalars ℂ := by
  ext value
  exact map_zero_iff selected hthree value

/-- Graded scalar extension identifies the entire positive tensor part with the coordinate ideal. -/
theorem tensor_positive_ideal (basis : letI := selected.rightAlgebra hthree
    Module.Basis I Schubert.Dihedral.CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod
          (Representation.trivial ℂ (DihedralGroup n) Schubert.Dihedral.CoordinatePolynomial)
          (representation selected hthree))
        (selected.splineRepresentation hthree),
      (∀ degree, (tensorPiece (P := Fin 2) (piece selected hthree) degree).map
        equivalence.toLinearMap = selected.piece degree) ∧
      (positiveTensor (P := Fin 2)).map equivalence.toLinearMap =
        (ideal selected hthree).restrictScalars ℂ ∧
      (∀ degree, (positiveTensor ⊓ tensorPiece (P := Fin 2) (piece selected hthree) degree).map
        equivalence.toLinearMap =
          (ideal selected hthree).restrictScalars ℂ ⊓ selected.piece degree) := by
  let := selected.rightAlgebra hthree
  obtain ⟨equivalence, hdegrees, hpure⟩ := tensor_free_augmentation selected hthree
    basis weights hbasis
  have hkernel := positive_tensor_map (quotientBasis selected hthree basis)
    equivalence.toLinearEquiv (quotientMap selected hthree).toLinearMap hpure
  rw [map_kernel_linear] at hkernel
  refine ⟨equivalence, hdegrees, hkernel, ?_⟩
  intro degree
  rw [Submodule.map_inf _ equivalence.toLinearEquiv.injective, hkernel, hdegrees]

end Right

end Schubert.Dihedral.RootSubset
