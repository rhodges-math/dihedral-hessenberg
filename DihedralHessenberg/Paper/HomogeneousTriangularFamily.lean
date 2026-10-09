import DihedralHessenberg.Paper.TriangularGradedQuotient
import DihedralHessenberg.Paper.TriangularHomogeneity

/-! # Homogeneous projection of an upper-triangular Hessenberg family -/

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

/-- Project each family vector to its Hessenberg inversion degree. -/
def hessenbergHomogeneousTriangularFamily (vertex : DihedralGroup n) : HessenbergSpline ideal :=
  (hessenbergGraph ideal).homogeneousComponent (hessenbergGraph_label_homogeneous ideal)
    (ideal.length vertex) (family vertex)

/-- The projected vector belongs to its prescribed Hessenberg degree. -/
theorem _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_mem (vertex :
  DihedralGroup n) :
    hessenbergHomogeneousTriangularFamily ideal family vertex ∈
      (hessenbergGraph ideal).homogeneousPiece (ideal.length vertex) :=
  (hessenbergGraph ideal).homogeneousComponent_mem _ _ _

include hsupport in
/-- Projection preserves the upper-triangular zeros. -/
theorem _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_support (first second :
  DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree first second) :
    (hessenbergHomogeneousTriangularFamily ideal family first :
      DihedralGroup n → CoordinatePolynomial) second = 0 := by
  change MvPolynomial.homogeneousComponent (ideal.length first)
    ((family first : DihedralGroup n → CoordinatePolynomial) second) = 0
  rw [hsupport first second hnot, map_zero]

include hsupport hdiagonal hdegree in
/-- Projection fixes every nonzero minimal-degree triangular diagonal. -/
theorem _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal (vertex :
  DihedralGroup n) :
    (hessenbergHomogeneousTriangularFamily ideal family vertex :
      DihedralGroup n → CoordinatePolynomial) vertex =
        (family vertex : DihedralGroup n → CoordinatePolynomial) vertex := by
  apply MvPolynomial.homogeneousComponent_eq_self
  apply _root_.Schubert.DihedralSplines.IndexedSpline.diagonal_homogeneous ideal (family vertex)
    vertex
  · intro lower hle hne
    apply hsupport vertex lower
    intro hback
    let := bruhatPartialOrder n hthree
    exact hne (le_antisymm hle hback)
  · exact hdiagonal vertex
  · exact hdegree vertex

include hsupport hdiagonal hdegree in
/-- Every qualifying triangular family gives the left quotient H-length degree counts. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_of_triangular (degree : ℕ)
  :
    Module.finrank ℂ (leftHessenbergQuotientPiece ideal degree) =
      Nat.card {vertex // ideal.length vertex = degree} := by
  apply _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_of_homogeneous_triangular
    ideal
    (hessenbergHomogeneousTriangularFamily ideal family)
  · exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_support ideal family
      hsupport
  · intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdiagonal vertex
  · intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdegree vertex
  · exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_mem ideal family

include hsupport hdiagonal hdegree in
/-- Every qualifying triangular family gives the same right quotient degree counts. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_of_triangular (degree : ℕ)
  :
    Module.finrank ℂ (rightHessenbergQuotientPiece ideal degree) =
      Nat.card {vertex // ideal.length vertex = degree} := by
  apply _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_of_homogeneous_triangular
    ideal
    (hessenbergHomogeneousTriangularFamily ideal family)
  · exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_support ideal family
      hsupport
  · intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdiagonal vertex
  · intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdegree vertex
  · exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_mem ideal family

end Schubert.DihedralSplines
