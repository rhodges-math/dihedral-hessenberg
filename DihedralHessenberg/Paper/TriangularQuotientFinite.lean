import DihedralHessenberg.Paper.TriangularBasis
import DihedralHessenberg.Splines.ReflectionQuotientFinite
import DihedralHessenberg.Paper.GradedQuotient

/-! # Finite Hessenberg quotients from triangular polynomial bases

These consequences assume the triangular family hypotheses. The explicit
construction of such families is still a separate theorem.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)
variable (family : DihedralGroup n → HessenbergSpline ideal)
variable (hsupport : ∀ first second, ¬ BruhatLE n hthree first second →
  (family first : DihedralGroup n → CoordinatePolynomial) second = 0)
variable (hdiagonal : ∀ vertex,
  (family vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
variable (hdegree : ∀ vertex,
  ((family vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
    ideal.length vertex)

include hsupport hdiagonal hdegree in
/-- A triangular family makes the left Hessenberg quotient finite over the complex field. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.finite_of_triangular :
    Module.Finite ℂ (LeftHessenbergQuotient ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralReflectionData n hthree).leftQuotient_finite_of_basis
    (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree)

include hsupport hdiagonal hdegree in
/-- A triangular family makes the right Hessenberg quotient finite over the complex field. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.finite_of_triangular :
    Module.Finite ℂ (RightHessenbergQuotient ideal) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  exact (dihedralReflectionData n hthree).rightQuotient_finite_of_basis
    (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree)

include hsupport hdiagonal hdegree in
/-- Every left homogeneous quotient piece is finite when a triangular family is given. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finite_of_triangular (degree : ℕ) :
    Module.Finite ℂ (leftHessenbergQuotientPiece ideal degree) := by
  let := _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.finite_of_triangular
    ideal family hsupport hdiagonal hdegree
  infer_instance

include hsupport hdiagonal hdegree in
/-- Every right homogeneous quotient piece is finite when a triangular family is given. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finite_of_triangular (degree : ℕ)
  :
    Module.Finite ℂ (rightHessenbergQuotientPiece ideal degree) := by
  let := _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.finite_of_triangular
    ideal family hsupport hdiagonal hdegree
  infer_instance

end Schubert.DihedralSplines
