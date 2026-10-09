import DihedralHessenberg.Paper.HomogeneousTriangularFamily
import DihedralHessenberg.Paper.HessenbergMultiplicity

/-! # Conditional explicit quotient Hilbert coefficients

The complete Hessenberg inversion distribution gives the Hilbert coefficients
of both quotients whenever a qualifying triangular spline family is supplied.
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
/-- The left quotient has the paper's parity-dependent coefficients under triangular hypotheses. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_piecewise_of_triangular
  (degree : ℕ) :
    Module.finrank ℂ (leftHessenbergQuotientPiece ideal degree) =
      if ideal.roots.card < degree then 0 else
      if degree = 0 ∨ degree = ideal.roots.card then 1 else
      if degree < ideal.roots.card / 2 ∨ ideal.roots.card - ideal.roots.card / 2 < degree
        then 2 else
      if Even ideal.roots.card then 2 * n - 2 * ideal.roots.card + 2
        else n - ideal.roots.card + 2 := by
  classical
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  rw [_root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.finrank_of_triangular
    ideal family hsupport hdiagonal hdegree]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    ideal.card_length_eq_piecewise degree
include hsupport hdiagonal hdegree in
/-- The right quotient has the parity-dependent coefficients under triangular hypotheses. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_piecewise_of_triangular
  (degree : ℕ) :
    Module.finrank ℂ (rightHessenbergQuotientPiece ideal degree) =
      if ideal.roots.card < degree then 0 else
      if degree = 0 ∨ degree = ideal.roots.card then 1 else
      if degree < ideal.roots.card / 2 ∨ ideal.roots.card - ideal.roots.card / 2 < degree
        then 2 else
      if Even ideal.roots.card then 2 * n - 2 * ideal.roots.card + 2
        else n - ideal.roots.card + 2 := by
  classical
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  rw [_root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.finrank_of_triangular
    ideal family hsupport hdiagonal hdegree]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    ideal.card_length_eq_piecewise degree

end Schubert.DihedralSplines
