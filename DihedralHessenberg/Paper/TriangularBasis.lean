import DihedralHessenberg.Splines.RightTriangularBasis
import DihedralHessenberg.Splines.BasisMinimality
import DihedralHessenberg.Paper.TriangularDivisibility

/-! # Both scalar bases from Hessenberg triangular families

The geometric label and canonical Bruhat bridges discharge residual divisibility.
Left elimination and the right-linear untwist transfer then provide two bases with
the same vectors. No explicit flow-up family or Hilbert formula is assumed.
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

include hsupport hdegree in
/-- Hessenberg triangular diagonals divide residual spline values. -/
theorem hessenberg_triangular_family_divides
    (value : HessenbergSpline ideal) (vertex : DihedralGroup n)
    (hzero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
      (value : DihedralGroup n → CoordinatePolynomial) lower = 0)
    (hvertex : (family vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) :
    (family vertex : DihedralGroup n → CoordinatePolynomial) vertex ∣
      (value : DihedralGroup n → CoordinatePolynomial) vertex := by
  apply hessenberg_diagonal_dvd_of_degree_bound ideal (family vertex) value vertex
  · intro lower hle hne
    apply hsupport vertex lower
    intro hback
    let := bruhatPartialOrder n hthree
    exact hne (le_antisymm hle hback)
  · exact hzero
  · exact hvertex
  · exact hdegree vertex

include hsupport hdiagonal hdegree in
/-- The upper-triangular family is a basis for constant polynomial scalars. -/
def hessenbergLeftTriangularBasis :
    Module.Basis (DihedralGroup n) CoordinatePolynomial (HessenbergSpline ideal) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  letI := bruhatPartialOrder n hthree
  letI := bruhatPartialOrder_wellFoundedLT n hthree
  exact (hessenbergGraph ideal).triangularBasis family hsupport hdiagonal
    (fun value vertex hzero =>
      hessenberg_triangular_family_divides ideal family hsupport hdegree value vertex
        (fun lower hle hne => hzero lower
          ((bruhatPartialOrder_lt n hthree lower vertex).2 ⟨hle, hne⟩)) (hdiagonal vertex))

include hsupport hdiagonal hdegree in
/-- The same family is a basis for orbit polynomial scalars. -/
def hessenbergRightTriangularBasis :
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
      (dihedralReflectionData n hthree).rightAlgebra
      (ideal.roots : Set (PositiveRootIndex n))
    Module.Basis (DihedralGroup n) CoordinatePolynomial (HessenbergSpline ideal) := by
  letI : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  letI := bruhatPartialOrder n hthree
  letI := bruhatPartialOrder_wellFoundedLT n hthree
  letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
    (dihedralReflectionData n hthree).rightAlgebra
    (ideal.roots : Set (PositiveRootIndex n))
  exact (dihedralReflectionData n hthree).rightTriangularBasis
    (ideal.roots : Set (PositiveRootIndex n)) family hsupport hdiagonal
    (fun value vertex hzero =>
      hessenberg_triangular_family_divides ideal family hsupport hdegree value vertex
        (fun lower hle hne => hzero lower
          ((bruhatPartialOrder_lt n hthree lower vertex).2 ⟨hle, hne⟩)) (hdiagonal vertex))

/-- The left triangular basis consists of the family vectors. -/
theorem hessenbergLeftTriangularBasis_apply (vertex : DihedralGroup n) :
    hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree vertex =
      family vertex := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := bruhatPartialOrder n hthree
  let := bruhatPartialOrder_wellFoundedLT n hthree
  unfold hessenbergLeftTriangularBasis
  exact (hessenbergGraph ideal).triangularBasis_apply _ _ _ _ vertex

/-- The right triangular basis consists of the family vectors. -/
theorem hessenbergRightTriangularBasis_apply (vertex : DihedralGroup n) :
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
      (dihedralReflectionData n hthree).rightAlgebra (ideal.roots : Set (PositiveRootIndex n))
    hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree vertex =
      family vertex := by
  let : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
    (dihedralReflectionData n hthree).rightAlgebra (ideal.roots : Set (PositiveRootIndex n))
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let := bruhatPartialOrder n hthree
  let := bruhatPartialOrder_wellFoundedLT n hthree
  unfold hessenbergRightTriangularBasis
  exact (dihedralReflectionData n hthree).rightTriangularBasis_apply _ _ _ _ _ vertex

include hsupport hdiagonal hdegree in
/-- Only the whole triangular family generates under constant polynomial scalars. -/
theorem hessenberg_left_triangular_minimal (indices : Set (DihedralGroup n)) :
    Submodule.span CoordinatePolynomial (family '' indices) = ⊤ ↔ indices = Set.univ := by
  let basis := hessenbergLeftTriangularBasis ideal family hsupport hdiagonal hdegree
  have hvectors : (basis : DihedralGroup n → HessenbergSpline ideal) = family :=
    funext (hessenbergLeftTriangularBasis_apply ideal family hsupport hdiagonal hdegree)
  rw [← hvectors]
  exact basis_span_image_eq_top_iff basis indices

include hsupport hdiagonal hdegree in
/-- Only the whole triangular family generates under orbit polynomial scalars. -/
theorem hessenberg_right_triangular_minimal (indices : Set (DihedralGroup n)) :
    letI : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
      (dihedralReflectionData n hthree).rightAlgebra (ideal.roots : Set (PositiveRootIndex n))
    Submodule.span CoordinatePolynomial (family '' indices) = ⊤ ↔ indices = Set.univ := by
  let : Algebra CoordinatePolynomial (HessenbergSpline ideal) :=
    (dihedralReflectionData n hthree).rightAlgebra (ideal.roots : Set (PositiveRootIndex n))
  let basis := hessenbergRightTriangularBasis ideal family hsupport hdiagonal hdegree
  have hvectors : (basis : DihedralGroup n → HessenbergSpline ideal) = family :=
    funext (hessenbergRightTriangularBasis_apply ideal family hsupport hdiagonal hdegree)
  rw [← hvectors]
  exact basis_span_image_eq_top_iff basis indices

end Schubert.DihedralSplines
