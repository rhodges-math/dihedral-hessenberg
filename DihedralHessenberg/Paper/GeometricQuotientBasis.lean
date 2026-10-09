import DihedralHessenberg.Paper.PaperQuotientGrading
import DihedralHessenberg.Splines.HomogeneousBasis
import DihedralHessenberg.Splines.PolynomialAlgebraQuotientBasis

/-! # Polynomial bases of geometric coordinate quotients -/

noncomputable section
namespace Schubert.Dihedral.RootSubset

open Schubert.Splines
variable {n : ℕ} {I : Type*} (selected : RootSubset n) (hthree : 3 ≤ n)
namespace Left


/-- A polynomial basis descends to its left quotient classes. -/
def quotientBasis (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) :
    Module.Basis I ℂ (Quotient selected hthree) := by
  let := selected.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => (selected.constantHom hthree).commutes _
  exact polynomialAlgebraQuotientBasis basis

/-- Descended basis vectors are their spline representatives. -/
theorem quotientBasis_apply (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (index : I) :
    quotientBasis selected hthree basis index = quotientMap selected hthree (basis index) := by
  let := selected.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => (selected.constantHom hthree).commutes _
  exact polynomialAlgebraQuotientBasis_apply basis index

/-- A descended vector retains its homogeneous degree. -/
theorem quotientBasis_mem_piece (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (degrees index)) (index : I) :
    quotientBasis selected hthree basis index ∈ piece selected hthree (degrees index) := by
  rw [quotientBasis_apply]
  exact (mem_piece selected hthree _ _).mpr ⟨basis index, hbasis index, rfl⟩

/-- The classes of one basis degree form that quotient homogeneous piece's basis. -/
def quotientPieceBasis [Fintype I] (basis : letI := selected.leftAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (degrees index)) (degree : ℕ) :
    Module.Basis {index // degrees index = degree} ℂ (piece selected hthree degree) := by
  letI := gradedAlgebra selected hthree
  exact homogeneousPieceBasis (piece selected hthree) (quotientBasis selected hthree basis)
    degrees (quotientBasis_mem_piece selected hthree basis degrees hbasis) degree
end Left

namespace Right


/-- A polynomial basis descends to its right quotient classes. -/
def quotientBasis (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) :
    Module.Basis I ℂ (Quotient selected hthree) := by
  let := selected.rightAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((selected.orbitHom hthree).commutes _).symm
  exact polynomialAlgebraQuotientBasis basis

/-- Descended basis vectors are their spline representatives. -/
theorem quotientBasis_apply (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (index : I) :
    quotientBasis selected hthree basis index = quotientMap selected hthree (basis index) := by
  let := selected.rightAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial selected.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((selected.orbitHom hthree).commutes _).symm
  exact polynomialAlgebraQuotientBasis_apply basis index

/-- A descended vector retains its homogeneous degree. -/
theorem quotientBasis_mem_piece (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (degrees index)) (index : I) :
    quotientBasis selected hthree basis index ∈ piece selected hthree (degrees index) := by
  rw [quotientBasis_apply]
  exact (mem_piece selected hthree _ _).mpr ⟨basis index, hbasis index, rfl⟩

/-- The classes of one basis degree form that quotient homogeneous piece's basis. -/
def quotientPieceBasis [Fintype I] (basis : letI := selected.rightAlgebra hthree
    Module.Basis I CoordinatePolynomial selected.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ selected.piece (degrees index)) (degree : ℕ) :
    Module.Basis {index // degrees index = degree} ℂ (piece selected hthree degree) := by
  letI := gradedAlgebra selected hthree
  exact homogeneousPieceBasis (piece selected hthree) (quotientBasis selected hthree basis)
    degrees (quotientBasis_mem_piece selected hthree basis degrees hbasis) degree
end Right

end Schubert.Dihedral.RootSubset
