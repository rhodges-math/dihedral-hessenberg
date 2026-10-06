import Schubert.Dihedral.PolynomialRepresentation
import Schubert.DihedralSplines.SplineScalarAction
import Schubert.DihedralSplines.SplineEquivariantBasis
import Schubert.FiniteGroupCharacters.TensorGrading
import Schubert.DihedralSplines.QuotientScalarAction

/-! # Augmentation-normalized graded scalar extension of geometric splines -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] {I : Type*} [Fintype I] [DecidableEq I]
variable (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- The homogeneous quotient lifts to a graded equivariant tensor decomposition. -/
theorem tensor_free_augmentation (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod (polynomialRepresentation n) (representation selected hthree))
        (selected.splineRepresentation hthree),
      (∀ degree, (Schubert.FiniteGroupCharacters.tensorPiece (P := Fin 2)
        (piece selected hthree) degree).map equivalence.toLinearMap = selected.piece degree) ∧
      (∀ polynomial (value : Quotient selected hthree),
        quotientMap selected hthree (equivalence (polynomial ⊗ₜ[ℂ] value)) =
          polynomial.constantCoeff • value) := by
  let := selected.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => (selected.constantHom hthree).commutes _
  obtain ⟨lift, hinverse, hhomogeneous, lifted, hlifted⟩ :=
    equivariant_basis selected hthree basis weights hbasis
  obtain ⟨equivalence, happly⟩ := Schubert.FiniteGroupCharacters.tensor_equiv_apply
    (polynomialRepresentation n) (representation selected hthree)
    (selected.splineRepresentation hthree) lift
    (fun element polynomial value => selected.left_smul_dot hthree element polynomial value)
    (quotientBasis selected hthree basis) lifted (fun index => (hlifted index).symm)
  have hlinear : equivalence.toLinearMap =
      (Schubert.FiniteGroupCharacters.tensorLift lift.toLinearMap).restrictScalars ℂ := by
    apply TensorProduct.ext'
    intro polynomial value
    exact happly polynomial value
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  refine ⟨equivalence, ?_, ?_⟩
  · intro degree
    rw [hlinear]
    exact Schubert.FiniteGroupCharacters.tensor_piece_map (piece selected hthree) selected.piece
      (quotientBasis selected hthree basis) lifted weights
      (quotientBasis_mem_piece selected hthree basis weights hbasis)
      (fun index => hlifted index ▸ hhomogeneous _ _
        (quotientBasis_mem_piece selected hthree basis weights hbasis index))
      lift.toLinearMap (fun index => (hlifted index).symm) hhomogeneous
      (fun scalarDegree valueDegree polynomial value hpolynomial hvalue =>
        smul_mem_piece selected hthree scalarDegree valueDegree polynomial hpolynomial value hvalue)
      degree
  · intro polynomial value
    rw [happly, quotientMap_smul, hinverse]

end Left

namespace Right

/-- The homogeneous quotient lifts to a graded equivariant tensor decomposition. -/
theorem tensor_free_augmentation (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    ∃ equivalence : Representation.Equiv
        (Representation.tprod
          (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
          (representation selected hthree))
        (selected.splineRepresentation hthree),
      (∀ degree, (Schubert.FiniteGroupCharacters.tensorPiece (P := Fin 2)
        (piece selected hthree) degree).map equivalence.toLinearMap = selected.piece degree) ∧
      (∀ polynomial (value : Quotient selected hthree),
        quotientMap selected hthree (equivalence (polynomial ⊗ₜ[ℂ] value)) =
          polynomial.constantCoeff • value) := by
  let := selected.rightAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((selected.orbitHom hthree).commutes _).symm
  obtain ⟨lift, hinverse, hhomogeneous, lifted, hlifted⟩ :=
    equivariant_basis selected hthree basis weights hbasis
  obtain ⟨equivalence, happly⟩ := Schubert.FiniteGroupCharacters.tensor_equiv_apply
    (Representation.trivial ℂ (DihedralGroup n) CoordinatePolynomial)
    (representation selected hthree)
    (selected.splineRepresentation hthree) lift
    (fun element polynomial value => selected.right_smul_dot hthree element polynomial value)
    (quotientBasis selected hthree basis) lifted (fun index => (hlifted index).symm)
  have hlinear : equivalence.toLinearMap =
      (Schubert.FiniteGroupCharacters.tensorLift lift.toLinearMap).restrictScalars ℂ := by
    apply TensorProduct.ext'
    intro polynomial value
    exact happly polynomial value
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  refine ⟨equivalence, ?_, ?_⟩
  · intro degree
    rw [hlinear]
    exact Schubert.FiniteGroupCharacters.tensor_piece_map (piece selected hthree) selected.piece
      (quotientBasis selected hthree basis) lifted weights
      (quotientBasis_mem_piece selected hthree basis weights hbasis)
      (fun index => hlifted index ▸ hhomogeneous _ _
        (quotientBasis_mem_piece selected hthree basis weights hbasis index))
      lift.toLinearMap (fun index => (hlifted index).symm) hhomogeneous
      (fun scalarDegree valueDegree polynomial value hpolynomial hvalue =>
        smul_mem_piece selected hthree scalarDegree valueDegree polynomial hpolynomial value hvalue)
      degree
  · intro polynomial value
    rw [happly, quotientMap_smul, hinverse]

end Right

end Schubert.Dihedral.RootSubset
