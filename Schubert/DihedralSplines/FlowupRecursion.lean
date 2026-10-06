import Schubert.DihedralSplines.HomogeneousFamily
import Schubert.DihedralSplines.SplineRestriction
import Schubert.DihedralSplines.HessenbergSupport
import Schubert.DihedralSplines.PaperTop

/-! # Recursive geometric Hessenberg flow-up splines -/

noncomputable section

open scoped Classical

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The identity flow-up spline is the constant one function. -/
def identity : HomogeneousAt ideal 1 where
  value := 1
  homogeneous := by
    rw [ideal.length_one]
    intro vertex
    exact MvPolynomial.isHomogeneous_one _ _
  support := fun vertex hnot => (hnot (one_bruhatLE n hthree vertex)).elim
  diagonal := one_ne_zero

/-- The selected transformed-product top spline is a homogeneous upper certificate. -/
def topCertificate : HomogeneousAt ideal (longestElement n hthree) where
  value := ideal.topSpline
  homogeneous := by
    rw [ideal.length_top]
    exact ideal.topSpline_mem_piece
  support := ideal.topSpline_support
  diagonal := ideal.topSpline_nonzero

/-- A full Schubert spline restricts to an H-upper certificate whenever its degrees agree. -/
def schubertAt (vertex : DihedralGroup n)
    (hdegree : ideal.toRootSubset.length vertex = length n hthree vertex) :
    HomogeneousAt ideal vertex where
  value := ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree vertex)
  homogeneous := by
    rw [hdegree]
    intro current
    exact SchubertSpline.homogeneous n hthree vertex current
  support := SchubertSpline.support n hthree vertex
  diagonal := SchubertSpline.diagonal n hthree vertex

/-- Flow-ups use Schubert restriction, upper-half divided difference, or equal-degree dot recursion.
-/
def construct (vertex : DihedralGroup n) : HomogeneousAt ideal vertex :=
  if hidentity : vertex = 1 then by
    subst vertex
    exact identity ideal
  else if htop : vertex = longestElement n hthree then by
    subst vertex
    exact topCertificate ideal
  else
    let alpha := SchubertSpline.ascentRoot n hthree vertex hidentity htop
    let hstep := SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop
    let hup : BruhatLE n hthree vertex (alpha.reflection * vertex) :=
      bruhatLE_of_length_lt n hthree (by rw [hstep.2]; omega)
    let hne : vertex ≠ alpha.reflection * vertex := by
      intro heq
      have hlength := hstep.2
      change length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1
        at hlength
      rw [← heq] at hlength
      omega
    if hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges then
      if hhalf : 2 * length n hthree vertex + 1 ≤ n then
        schubertAt ideal vertex (ideal.length_full alpha hstep.1 vertex hup hne hhalf hedge)
      else
        let tail := construct (alpha.reflection * vertex)
        HomogeneousAt.differenceStep alpha hstep.1 hstep.2 tail
          (by
            intro current hnonzero
            apply ideal.edge_above alpha hstep.1 vertex hstep.2 (by omega) hedge current
            by_contra hnot
            exact hnonzero (tail.support current hnot))
          (ideal.length_edge alpha hstep.1 vertex hup hne hedge).symm
    else
      HomogeneousAt.dotStep alpha hstep.1 hstep.2
        (construct (alpha.reflection * vertex))
        (by
          change (ideal.toRootSubset.inversions (alpha.reflection * vertex)).ncard =
            (ideal.toRootSubset.inversions vertex).ncard
          rw [ideal.inversions_no_edge alpha hstep.1 vertex hup hne hedge])
termination_by n - length n hthree vertex
decreasing_by
  all_goals
    have _hstep := (SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop).2
    have hbound := length_le_polygon_parameter n hthree
      ((SchubertSpline.ascentRoot n hthree vertex hidentity htop).reflection * vertex)
    omega

/-- The flow-up function is the value of its constructed upper certificate. -/
def spline (vertex : DihedralGroup n) : ideal.toRootSubset.Spline :=
  (construct ideal vertex).value

/-- The constructed flow-up functions form a triangular family. -/
def family : TriangularFamily ideal := HomogeneousAt.family (construct ideal)

/-- The family vectors are exactly the recursive flow-up functions. -/
theorem family_value (vertex : DihedralGroup n) : (family ideal).value vertex =
    spline ideal vertex := rfl

end Schubert.DihedralSplines.FlowupSpline
