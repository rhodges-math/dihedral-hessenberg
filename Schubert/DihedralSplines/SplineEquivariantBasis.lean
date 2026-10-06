import Schubert.Splines.PolynomialAlgebraCoordinates
import Schubert.DihedralSplines.SplineGradedSection
import Schubert.DihedralSplines.GeometricQuotientBasis
import Schubert.DihedralSplines.PaperCoordinates

/-! # Homogeneous equivariant lifts of geometric quotient bases -/

noncomputable section
namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} [NeZero n] {I : Type*} [Fintype I] [DecidableEq I]
variable (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- A graded equivariant section lifts the quotient basis to a polynomial basis. -/
theorem equivariant_basis (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    letI := selected.leftAlgebra hthree
    ∃ lift : (representation selected hthree).IntertwiningMap
        (selected.splineRepresentation hthree),
      (∀ value, quotientMap selected hthree (lift value) = value) ∧
      (∀ degree (value : Quotient selected hthree), value ∈ piece selected hthree degree →
        lift value ∈ selected.piece degree) ∧
      ∃ lifted : Module.Basis I CoordinatePolynomial selected.Spline,
        ∀ index, lifted index = lift (quotientBasis selected hthree basis index) := by
  let := selected.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => (selected.constantHom hthree).commutes _
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  obtain ⟨lift, hinverse, hhomogeneous⟩ := graded_section selected hthree
  let values index := lift (quotientBasis selected hthree basis index)
  have hvalues : ∀ index, values index ∈ selected.piece (weights index) := by
    intro index
    exact hhomogeneous _ _ (quotientBasis_mem_piece selected hthree basis weights hbasis index)
  have hclasses : ∀ index,
      Ideal.Quotient.mk (Ideal.map (algebraMap CoordinatePolynomial selected.Spline)
        (MvPolynomial.idealOfVars (Fin 2) ℂ)) (values index) =
      Ideal.Quotient.mk _ (basis index) := by
    intro index
    change quotientMap selected hthree (values index) = quotientMap selected hthree (basis index)
    rw [hinverse, quotientBasis_apply]
  obtain ⟨lifted, hlifted⟩ := Schubert.Splines.homogeneous_algebra_basis_lift selected.piece
    basis weights hbasis
    (fun scalarDegree valueDegree polynomial value hpolynomial hvalue =>
      smul_mem_piece selected hthree scalarDegree valueDegree polynomial hpolynomial value hvalue)
    values hvalues hclasses
  exact ⟨lift, hinverse, hhomogeneous, lifted, hlifted⟩

end Left

namespace Right

/-- A graded equivariant section lifts the quotient basis to a polynomial basis. -/
theorem equivariant_basis (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (weights index)) :
    letI := selected.rightAlgebra hthree
    ∃ lift : (representation selected hthree).IntertwiningMap
        (selected.splineRepresentation hthree),
      (∀ value, quotientMap selected hthree (lift value) = value) ∧
      (∀ degree (value : Quotient selected hthree), value ∈ piece selected hthree degree →
        lift value ∈ selected.piece degree) ∧
      ∃ lifted : Module.Basis I CoordinatePolynomial selected.Spline,
        ∀ index, lifted index = lift (quotientBasis selected hthree basis index) := by
  let := selected.rightAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((selected.orbitHom hthree).commutes _).symm
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  obtain ⟨lift, hinverse, hhomogeneous⟩ := graded_section selected hthree
  let values index := lift (quotientBasis selected hthree basis index)
  have hvalues : ∀ index, values index ∈ selected.piece (weights index) := by
    intro index
    exact hhomogeneous _ _ (quotientBasis_mem_piece selected hthree basis weights hbasis index)
  have hclasses : ∀ index,
      Ideal.Quotient.mk (Ideal.map (algebraMap CoordinatePolynomial selected.Spline)
        (MvPolynomial.idealOfVars (Fin 2) ℂ)) (values index) =
      Ideal.Quotient.mk _ (basis index) := by
    intro index
    change quotientMap selected hthree (values index) = quotientMap selected hthree (basis index)
    rw [hinverse, quotientBasis_apply]
  obtain ⟨lifted, hlifted⟩ := Schubert.Splines.homogeneous_algebra_basis_lift selected.piece
    basis weights hbasis
    (fun scalarDegree valueDegree polynomial value hpolynomial hvalue =>
      smul_mem_piece selected hthree scalarDegree valueDegree polynomial hpolynomial value hvalue)
    values hvalues hclasses
  exact ⟨lift, hinverse, hhomogeneous, lifted, hlifted⟩

end Right

end Schubert.Dihedral.RootSubset
