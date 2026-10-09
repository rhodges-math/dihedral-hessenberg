import DihedralHessenberg.Paper.PaperScalarTransport
import DihedralHessenberg.Paper.PaperQuotientGrading
import DihedralHessenberg.Splines.HomogeneousGenerators
import DihedralHessenberg.Splines.SplineInfinitude
import DihedralHessenberg.Splines.QuotientPieceFinite

/-! # Finiteness and homogeneous generators of geometric spline modules -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Constant polynomials force the geometric spline algebra to have infinite complex dimension. -/
theorem not_moduleFinite (hthree : 3 ≤ n) : ¬ Module.Finite ℂ selected.Spline := by
  intro hfinite
  let := hfinite
  let := Module.Finite.equiv (selected.backendEquiv hthree).toLinearEquiv
  exact (dihedralReflectionData n hthree).spline_not_moduleFinite selected.indices inferInstance

namespace Left

/-- Constant polynomial scalars admit a finite homogeneous generating set. -/
theorem homogeneous_generators :
    letI := selected.leftAlgebra hthree
    ∃ generators : Finset selected.Spline,
      Submodule.span CoordinatePolynomial (generators : Set selected.Spline) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree, value ∈ selected.piece degree := by
  let := selected.leftAlgebra hthree
  let := module_finite selected hthree
  let := selected.gradedAlgebra hthree
  exact exists_homogeneous_generators selected.piece

/-- Every homogeneous geometric left quotient piece is finite without a basis hypothesis. -/
theorem piece_finite (degree : ℕ) : Module.Finite ℂ (piece selected hthree degree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := (dihedralGradedReflectionData n hthree).leftQuotientPiece_finite selected.indices degree
  exact Module.Finite.equiv (pieceEquiv selected hthree degree).symm

end Left

namespace Right

/-- Orbit polynomial scalars admit a finite homogeneous generating set. -/
theorem homogeneous_generators :
    letI := selected.rightAlgebra hthree
    ∃ generators : Finset selected.Spline,
      Submodule.span CoordinatePolynomial (generators : Set selected.Spline) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree, value ∈ selected.piece degree := by
  let := selected.rightAlgebra hthree
  let := module_finite selected hthree
  let := selected.gradedAlgebra hthree
  exact exists_homogeneous_generators selected.piece

/-- Every homogeneous geometric right quotient piece is finite without a basis hypothesis. -/
theorem piece_finite (degree : ℕ) : Module.Finite ℂ (piece selected hthree degree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := (dihedralGradedReflectionData n hthree).rightQuotientPiece_finite selected.indices degree
  exact Module.Finite.equiv (pieceEquiv selected hthree degree).symm

end Right

end Schubert.Dihedral.RootSubset
