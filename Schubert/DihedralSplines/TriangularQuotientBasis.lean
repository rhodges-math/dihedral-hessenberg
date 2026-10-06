import Schubert.DihedralSplines.TriangularBasis
import Schubert.DihedralSplines.Quotient
import Schubert.Splines.ReflectionQuotientBasis

/-! # Quotient bases from Hessenberg triangular families

Both polynomial scalar bases descend to complex quotient bases. Their dimensions
are exactly twice the polygon parameter. A qualifying triangular family remains
an explicit hypothesis; its flow-up construction is separate.
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

include hsupport hdiagonal hdegree in
/-- The left quotient basis consists of classes of the triangular family. -/
def leftHessenbergTriangularQuotientBasis :
    Module.Basis (DihedralGroup n) ℂ (LeftHessenbergQuotient ideal) :=
  (dihedralReflectionData n hthree).leftQuotientBasis (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree)

include hsupport hdiagonal hdegree in
/-- The right quotient basis consists of classes of the same triangular family. -/
def rightHessenbergTriangularQuotientBasis :
    Module.Basis (DihedralGroup n) ℂ (RightHessenbergQuotient ideal) :=
  (dihedralReflectionData n hthree).rightQuotientBasis (ideal.roots : Set (PositiveRootIndex n))
    (hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree)

/-- Each left triangular quotient basis vector is the spline's class. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.TriangularQuotientBasis.apply (vertex :
  DihedralGroup n) :
    leftHessenbergTriangularQuotientBasis ideal family hsupport hdiagonal hdegree vertex =
      leftHessenbergQuotientMap ideal (family vertex) :=
  ((dihedralReflectionData n hthree).leftQuotientBasis_apply
    (ideal.roots : Set (PositiveRootIndex n)) _ vertex).trans
    (congrArg (leftHessenbergQuotientMap ideal)
      (hessenbergLeftTriangularBasis_apply ideal family hsupport hdiagonal hdegree vertex))

/-- Each right triangular quotient basis vector is the spline's class. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.TriangularQuotientBasis.apply (vertex :
  DihedralGroup n) :
    rightHessenbergTriangularQuotientBasis ideal family hsupport hdiagonal hdegree vertex =
      rightHessenbergQuotientMap ideal (family vertex) :=
  ((dihedralReflectionData n hthree).rightQuotientBasis_apply
    (ideal.roots : Set (PositiveRootIndex n)) _ vertex).trans
    (congrArg (rightHessenbergQuotientMap ideal)
      (hessenbergRightTriangularBasis_apply ideal family hsupport hdiagonal hdegree vertex))

include hsupport hdiagonal hdegree in
/-- The left quotient of a qualifying triangular family has dimension twice the group parameter. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.finrank_of_triangular :
    Module.finrank ℂ (LeftHessenbergQuotient ideal) = 2 * n := by
  rw [Module.finrank_eq_nat_card_basis
    (leftHessenbergTriangularQuotientBasis ideal family hsupport hdiagonal hdegree),
    DihedralGroup.nat_card]

include hsupport hdiagonal hdegree in
/-- The right quotient of a qualifying triangular family has dimension twice the group parameter. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.finrank_of_triangular :
    Module.finrank ℂ (RightHessenbergQuotient ideal) = 2 * n := by
  rw [Module.finrank_eq_nat_card_basis
    (rightHessenbergTriangularQuotientBasis ideal family hsupport hdiagonal hdegree),
    DihedralGroup.nat_card]

end Schubert.DihedralSplines
