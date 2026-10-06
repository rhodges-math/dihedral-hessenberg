import Schubert.Splines.QuotientPieceFinite
import Schubert.DihedralSplines.GradedQuotient

/-! # Unconditional finite degree pieces of Hessenberg splines and both quotients -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- A Hessenberg spline degree piece is finite without a triangular family assumption. -/
theorem hessenbergSplinePiece_finite (degree : ℕ) :
    Module.Finite ℂ ((hessenbergGraph ideal).homogeneousPiece degree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (hessenbergGraph ideal).homogeneousPiece_finite degree

/-- Each left Hessenberg quotient degree piece is unconditionally finite. -/
theorem leftHessenbergQuotientPiece_finite (degree : ℕ) :
    Module.Finite ℂ (leftHessenbergQuotientPiece ideal degree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralGradedReflectionData n hthree).leftQuotientPiece_finite
    (ideal.roots : Set (PositiveRootIndex n)) degree

/-- Each right Hessenberg quotient degree piece is unconditionally finite. -/
theorem rightHessenbergQuotientPiece_finite (degree : ℕ) :
    Module.Finite ℂ (rightHessenbergQuotientPiece ideal degree) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralGradedReflectionData n hthree).rightQuotientPiece_finite
    (ideal.roots : Set (PositiveRootIndex n)) degree

end Schubert.DihedralSplines
