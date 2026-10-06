import Schubert.Splines.PolynomialSplineHilbert
import Schubert.DihedralSplines.HomogeneousTriangularFamily

/-! # Conditional homogeneous dimensions of the full Hessenberg spline algebra -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} [NeZero n] {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- A qualifying triangular family gives the full spline Hilbert coefficient convolution. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Piece.finrank_of_triangular
    (family : DihedralGroup n → HessenbergSpline ideal)
    (hsupport : ∀ first second, ¬ BruhatLE n hthree first second →
      (family first : DihedralGroup n → CoordinatePolynomial) second = 0)
    (hdiagonal : ∀ vertex,
      (family vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hdegree : ∀ vertex,
      ((family vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
        ideal.length vertex) (degree : ℕ) :
    Module.finrank ℂ ((hessenbergGraph ideal).homogeneousPiece degree) =
      ∑ vertex : DihedralGroup n,
        if ideal.length vertex ≤ degree then degree - ideal.length vertex + 1 else 0 := by
  let projected := hessenbergHomogeneousTriangularFamily ideal family
  have hsupport' : ∀ first second, ¬ BruhatLE n hthree first second →
      (projected first : DihedralGroup n → CoordinatePolynomial) second = 0 :=
    _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_support ideal family hsupport
  have hdiagonal' : ∀ vertex,
      (projected vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
    intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdiagonal vertex
  have hdegree' : ∀ vertex,
      ((projected vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
        ideal.length vertex := by
    intro vertex
    rw [_root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal
      ideal family hsupport hdiagonal hdegree]
    exact hdegree vertex
  apply (hessenbergGraph ideal).piece_finrank_convolution
    (hessenbergGraph_label_homogeneous ideal)
    (hessenbergLeftTriangularBasis ideal projected hsupport' hdiagonal' hdegree') ideal.length
  intro vertex
  rw [hessenbergLeftTriangularBasis_apply]
  exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_mem ideal family vertex

end Schubert.DihedralSplines
