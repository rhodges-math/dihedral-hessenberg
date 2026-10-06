import Schubert.DihedralSplines.PaperIdeal
import Schubert.DihedralSplines.TriangularHomogeneity

/-! # Upper-triangular families of geometric splines -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

/-- An upper-triangular family with the prescribed whole-spline Hessenberg degrees. -/
structure TriangularFamily {n : ℕ} {hthree : 3 ≤ n} [NeZero n]
    (ideal : HessenbergIdeal n hthree) where
  /-- The spline at each vertex. -/
  value : DihedralGroup n → ideal.toRootSubset.Spline
  /-- Each spline is supported only above its indexing vertex. -/
  support : ∀ first second, ¬ BruhatLE n hthree first second →
    (value first : DihedralGroup n → CoordinatePolynomial) second = 0
  /-- Each indexing vertex belongs to the support of its spline. -/
  diagonal : ∀ vertex, (value vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0
  /-- The maximum degree of all vertex values is the selected-inversion count. -/
  degree_eq : ∀ vertex, ideal.toRootSubset.degree (value vertex) = ideal.toRootSubset.length vertex

namespace TriangularFamily

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

/-- Every value in a triangular spline has the prescribed whole-spline degree bound. -/
theorem bound (family : TriangularFamily ideal) (vertex current : DihedralGroup n) :
    ((family.value vertex : DihedralGroup n → CoordinatePolynomial) current).totalDegree ≤
      ideal.toRootSubset.length vertex :=
  (ideal.toRootSubset.degree_le_iff _ _).mp (le_of_eq (family.degree_eq vertex)) current

/-- The direct whole-spline degree hypothesis implies the indexed diagonal bound. -/
theorem diagonal_bound (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    ((family.value vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
      ideal.indexed.length vertex := by
  rw [← ideal.length_indexed]
  exact family.bound vertex vertex

/-- Nonzero triangular diagonals force equality in a whole-spline degree bound. -/
theorem degree_eq_of_bound (value : DihedralGroup n → ideal.toRootSubset.Spline)
    (hsupport : ∀ first second, ¬ BruhatLE n hthree first second →
      (value first : DihedralGroup n → CoordinatePolynomial) second = 0)
    (hdiagonal : ∀ vertex, (value vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hbound : ∀ vertex current,
      ((value vertex : DihedralGroup n → CoordinatePolynomial) current).totalDegree ≤
        ideal.toRootSubset.length vertex) (vertex : DihedralGroup n) :
    ideal.toRootSubset.degree (value vertex) = ideal.toRootSubset.length vertex := by
  have hhomogeneous := _root_.Schubert.DihedralSplines.IndexedSpline.diagonal_homogeneous
    ideal.indexed
    (ideal.splineEquiv (value vertex)) vertex
    (by
      intro lower hle hne
      apply hsupport vertex lower
      intro hback
      let := bruhatPartialOrder n hthree
      exact hne (le_antisymm hle hback))
    (hdiagonal vertex)
    (by rw [← ideal.length_indexed]; exact hbound vertex vertex)
  have hdegree := hhomogeneous.totalDegree (hdiagonal vertex)
  change ((value vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree =
    ideal.indexed.length vertex at hdegree
  rw [← ideal.length_indexed] at hdegree
  apply le_antisymm ((ideal.toRootSubset.degree_le_iff _ _).mpr (hbound vertex))
  rw [← hdegree]
  exact Finset.le_sup (f := fun current =>
    ((value vertex : DihedralGroup n → CoordinatePolynomial) current).totalDegree)
    (Finset.mem_univ vertex)

/-- The whole-spline equality is equivalent to the universal value bound for a triangular family.
-/
theorem degree_iff_bound (value : DihedralGroup n → ideal.toRootSubset.Spline)
    (hsupport : ∀ first second, ¬ BruhatLE n hthree first second →
      (value first : DihedralGroup n → CoordinatePolynomial) second = 0)
    (hdiagonal : ∀ vertex, (value vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) :
    (∀ vertex, ideal.toRootSubset.degree (value vertex) = ideal.toRootSubset.length vertex) ↔
      ∀ vertex current,
        ((value vertex : DihedralGroup n → CoordinatePolynomial) current).totalDegree ≤
          ideal.toRootSubset.length vertex := by
  constructor
  · intro hdegree vertex
    exact (ideal.toRootSubset.degree_le_iff _ _).mp (le_of_eq (hdegree vertex))
  · intro hbound vertex
    exact degree_eq_of_bound value hsupport hdiagonal hbound vertex

/-- A triangular family can be constructed from the equivalent universal degree bounds. -/
def ofBound (value : DihedralGroup n → ideal.toRootSubset.Spline)
    (hsupport : ∀ first second, ¬ BruhatLE n hthree first second →
      (value first : DihedralGroup n → CoordinatePolynomial) second = 0)
    (hdiagonal : ∀ vertex, (value vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hbound : ∀ vertex current,
      ((value vertex : DihedralGroup n → CoordinatePolynomial) current).totalDegree ≤
        ideal.toRootSubset.length vertex) : TriangularFamily ideal where
  value := value
  support := hsupport
  diagonal := hdiagonal
  degree_eq := degree_eq_of_bound value hsupport hdiagonal hbound

end TriangularFamily

end Schubert.DihedralSplines
