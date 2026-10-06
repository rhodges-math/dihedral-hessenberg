import Schubert.DihedralSplines.TriangularQuotientBasis
import Schubert.DihedralSplines.GradedQuotient
import Schubert.Splines.GradedQuotientBasis

/-! # Degree dimensions of homogeneous triangular Hessenberg families

A qualifying triangular family that is homogeneous in its Hessenberg inversion
length gives both quotient degree bases. Explicit family existence remains separate.
-/

noncomputable section

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
variable (hhomogeneous : ∀ vertex,
  family vertex ∈ (hessenbergGraph ideal).homogeneousPiece (ideal.length vertex))

include hsupport hdiagonal hdegree hhomogeneous in
/-- Homogeneous triangular classes of one length form a left quotient degree basis. -/
def leftHessenbergTriangularPieceBasis (degree : ℕ) :
    Module.Basis {vertex // ideal.length vertex = degree} ℂ
      (leftHessenbergQuotientPiece ideal degree) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply (dihedralGradedReflectionData n hthree).leftQuotientPieceBasis
    (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree) ideal.length
  intro vertex
  change (hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree) vertex ∈
    (hessenbergGraph ideal).homogeneousPiece (ideal.length vertex)
  rw [hessenbergLeftTriangularBasis_apply]
  exact hhomogeneous vertex

include hsupport hdiagonal hdegree hhomogeneous in
/-- Homogeneous triangular classes of one length form a right quotient degree basis. -/
def rightHessenbergTriangularPieceBasis (degree : ℕ) :
    Module.Basis {vertex // ideal.length vertex = degree} ℂ
      (rightHessenbergQuotientPiece ideal degree) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply (dihedralGradedReflectionData n hthree).rightQuotientPieceBasis
    (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree) ideal.length
  intro vertex
  change (hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree) vertex ∈
    (hessenbergGraph ideal).homogeneousPiece (ideal.length vertex)
  rw [hessenbergRightTriangularBasis_apply]
  exact hhomogeneous vertex

include hsupport hdiagonal hdegree hhomogeneous in
/-- The conditional left quotient Hilbert coefficient is its Hessenberg length fiber. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_of_homogeneous_triangular
  (degree : ℕ) :
    Module.finrank ℂ (leftHessenbergQuotientPiece ideal degree) =
      Nat.card {vertex // ideal.length vertex = degree} :=
  Module.finrank_eq_nat_card_basis
    (leftHessenbergTriangularPieceBasis ideal family hsupport hdiagonal hdegree hhomogeneous degree)

include hsupport hdiagonal hdegree hhomogeneous in
/-- The conditional right quotient Hilbert coefficient is the same length fiber. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_of_homogeneous_triangular
  (degree : ℕ) :
    Module.finrank ℂ (rightHessenbergQuotientPiece ideal degree) =
      Nat.card {vertex // ideal.length vertex = degree} :=
  Module.finrank_eq_nat_card_basis
    (rightHessenbergTriangularPieceBasis ideal family hsupport hdiagonal hdegree
      hhomogeneous degree)

end Schubert.DihedralSplines
