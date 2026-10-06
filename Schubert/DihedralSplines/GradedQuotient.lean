import Schubert.DihedralSplines.Quotient
import Schubert.DihedralSplines.Grading
import Schubert.Splines.QuotientRepresentation

/-! # Graded dot representations on the Hessenberg quotients

The quotient degree pieces are images of homogeneous Hessenberg splines. Both defining
ideals are homogeneous and dot-stable; the generic construction specializes to the
dihedral reflection data and supplies complex representations on every quotient piece.
-/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- The degree piece of the left Hessenberg quotient. -/
def leftHessenbergQuotientPiece (degree : ℕ) :
    Submodule ℂ (LeftHessenbergQuotient ideal) :=
  (dihedralGradedReflectionData n hthree).leftQuotientPiece
    (ideal.roots : Set (PositiveRootIndex n)) degree

/-- The degree piece of the right Hessenberg quotient. -/
def rightHessenbergQuotientPiece (degree : ℕ) :
    Submodule ℂ (RightHessenbergQuotient ideal) :=
  (dihedralGradedReflectionData n hthree).rightQuotientPiece
    (ideal.roots : Set (PositiveRootIndex n)) degree

/-- The polynomial degree grading on the left Hessenberg quotient. -/
@[instance_reducible]
def leftHessenbergQuotientGradedAlgebra :
    GradedAlgebra (leftHessenbergQuotientPiece ideal) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralGradedReflectionData n hthree).leftQuotientGradedAlgebra
    (ideal.roots : Set (PositiveRootIndex n))

/-- The polynomial degree grading on the right Hessenberg quotient. -/
@[instance_reducible]
def rightHessenbergQuotientGradedAlgebra :
    GradedAlgebra (rightHessenbergQuotientPiece ideal) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralGradedReflectionData n hthree).rightQuotientGradedAlgebra
    (ideal.roots : Set (PositiveRootIndex n))

/-- The dot representation on each degree of the left Hessenberg quotient. -/
def _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (leftHessenbergQuotientPiece ideal degree) :=
  (dihedralGradedReflectionData n hthree).leftQuotientPieceRepresentation
    (ideal.roots : Set (PositiveRootIndex n)) degree

/-- The dot representation on each degree of the right Hessenberg quotient. -/
def _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (rightHessenbergQuotientPiece ideal degree) :=
  (dihedralGradedReflectionData n hthree).rightQuotientPieceRepresentation
    (ideal.roots : Set (PositiveRootIndex n)) degree

end Schubert.DihedralSplines
