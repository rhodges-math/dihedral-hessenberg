import Schubert.DihedralSplines.SchubertConstruction
import Schubert.DihedralSplines.SchubertOperators
import Schubert.Dihedral.AscentSupport
import Schubert.Dihedral.RootNormal

/-! # Homogeneous upper-spline recursion steps -/

noncomputable section

namespace Schubert.DihedralSplines.HomogeneousAt

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}
variable {element : DihedralGroup n} (alpha : PositiveRoot n)
variable (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
variable (hascent : length n hthree (alpha.reflection * element) =
  length n hthree element + 1)

/-- Dot translation of an upper spline gives the equal-degree recursion step. -/
def dotStep (tail : HomogeneousAt ideal (alpha.reflection * element))
    (hdegree : ideal.toRootSubset.length (alpha.reflection * element) =
      ideal.toRootSubset.length element) : HomogeneousAt ideal element where
  value := ideal.toRootSubset.dot hthree alpha.reflection tail.value
  homogeneous := by
    rw [← hdegree]
    exact ideal.toRootSubset.dot_mem_piece hthree alpha.reflection _ _ tail.homogeneous
  support := by
    intro vertex hnot
    rw [RootSubset.dot_apply, alpha.reflection_inv]
    rw [tail.support _ (ascent_support alpha hsimple element vertex hascent hnot).2]
    exact map_zero _
  diagonal := by
    rw [RootSubset.dot_apply, alpha.reflection_inv]
    intro hzero
    apply tail.diagonal
    apply (polynomialAction n alpha.reflection).injective
    simpa only [map_zero] using hzero

/-- An admissible divided difference gives the one-degree-lower recursion step. -/
def differenceStep (tail : HomogeneousAt ideal (alpha.reflection * element))
    (hedges : ∀ vertex,
      (tail.value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
        (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hdegree : ideal.toRootSubset.length (alpha.reflection * element) =
      ideal.toRootSubset.length element + 1) : HomogeneousAt ideal element where
  value := ideal.dividedDifference tail.value alpha hedges
  homogeneous := ideal.dividedDifference_mem_piece tail.value alpha hedges _
    (by rw [← hdegree]; exact tail.homogeneous)
  support := by
    intro vertex hnot
    have hexclusions := ascent_support alpha hsimple element vertex hascent hnot
    have hmul := ideal.dividedDifference_mul tail.value alpha hedges vertex
    rw [tail.support vertex hexclusions.1, RootSubset.dot_apply, alpha.reflection_inv,
      tail.support _ hexclusions.2, map_zero, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left alpha.form_ne_zero
  diagonal := by
    have hexclusion : ¬ BruhatLE n hthree (alpha.reflection * element) element := by
      intro hle
      have hlength := bruhatLE_length_le n hthree hle
      omega
    have hmul := ideal.dividedDifference_mul tail.value alpha hedges element
    rw [tail.support element hexclusion, RootSubset.dot_apply, alpha.reflection_inv,
      zero_sub] at hmul
    intro hzero
    rw [hzero, mul_zero] at hmul
    have himage : polynomialAction n alpha.reflection
        ((tail.value : DihedralGroup n → CoordinatePolynomial)
          (alpha.reflection * element)) = 0 := neg_eq_zero.mp hmul.symm
    apply tail.diagonal
    apply (polynomialAction n alpha.reflection).injective
    simpa only [map_zero] using himage

end Schubert.DihedralSplines.HomogeneousAt
