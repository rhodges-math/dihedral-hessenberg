import Schubert.DihedralSplines.SchubertRecursion
import Schubert.DihedralSplines.TriangularFamily

/-! # Families of homogeneous geometric upper splines -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

namespace HomogeneousAt

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}
variable {vertex : DihedralGroup n}

/-- Nonzero homogeneous upper splines have exactly their prescribed whole-spline degree. -/
theorem degree_eq (value : HomogeneousAt ideal vertex) :
    ideal.toRootSubset.degree value.value = ideal.toRootSubset.length vertex := by
  classical
  apply le_antisymm
  · apply (ideal.toRootSubset.degree_le_iff _ _).mpr
    intro current
    exact (value.homogeneous current).totalDegree_le
  · rw [← (value.homogeneous vertex).totalDegree value.diagonal]
    exact Finset.le_sup (f := fun current =>
      ((value.value : DihedralGroup n → CoordinatePolynomial) current).totalDegree)
      (Finset.mem_univ vertex)

/-- A constructed homogeneous certificate family gives a vector triangular family. -/
def family (values : ∀ vertex, HomogeneousAt ideal vertex) : TriangularFamily ideal where
  value := fun vertex => (values vertex).value
  support := fun vertex => (values vertex).support
  diagonal := fun vertex => (values vertex).diagonal
  degree_eq := fun vertex => (values vertex).degree_eq

end HomogeneousAt

namespace SchubertSpline

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- The recursively constructed Schubert splines form the full-root triangular family. -/
def family : TriangularFamily (HessenbergIdeal.full n hthree) :=
  HomogeneousAt.family (construct n hthree)

/-- The vectors of this family are the recursively constructed Schubert splines.
-/
theorem family_value (vertex : DihedralGroup n) : (family n hthree).value vertex =
    spline n hthree vertex := rfl

end SchubertSpline

end Schubert.DihedralSplines
