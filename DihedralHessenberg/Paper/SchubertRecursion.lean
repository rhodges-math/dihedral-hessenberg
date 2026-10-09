import DihedralHessenberg.Paper.FlowupSteps
import DihedralHessenberg.Paper.RootFullDegree

/-! # Downward recursion for geometric Schubert splines -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- The identity Schubert spline is the constant one function. -/
def identity : HomogeneousAt (HessenbergIdeal.full n hthree) 1 where
  value := 1
  homogeneous := by
    change 1 ∈ (RootSubset.full n).piece ((RootSubset.full n).length 1)
    rw [RootSubset.length_full n hthree, Schubert.Dihedral.length_one]
    intro vertex
    exact MvPolynomial.isHomogeneous_one _ _
  support := by
    intro vertex hnot
    exact (hnot (one_bruhatLE n hthree vertex)).elim
  diagonal := one_ne_zero

/-- The positive-form Schubert top has the required full inversion degree. -/
def topCertificate : HomogeneousAt (HessenbergIdeal.full n hthree)
    (longestElement n hthree) where
  value := top n hthree
  homogeneous := by
    change top n hthree ∈ (RootSubset.full n).piece
      ((RootSubset.full n).length (longestElement n hthree))
    rw [RootSubset.length_full n hthree,
      (length_eq_longest n hthree _).mpr rfl]
    exact top_homogeneous n hthree
  support := top_support n hthree
  diagonal := top_nonzero n hthree

omit [NeZero n] in
/-- The unique simple-vector ascent chosen at a nonendpoint vertex. -/
def ascentRoot (vertex : DihedralGroup n) (hneOne : vertex ≠ 1)
    (hneTop : vertex ≠ longestElement n hthree) : PositiveRoot n :=
  Classical.choose (unique_root_ascent n hthree vertex hneOne hneTop)

omit [NeZero n] in
/-- The chosen vector is simple and raises the canonical length by one. -/
theorem ascentRoot_spec (vertex : DihedralGroup n) (hneOne : vertex ≠ 1)
    (hneTop : vertex ≠ longestElement n hthree) :
    (ascentRoot n hthree vertex hneOne hneTop = simpleRoot n hthree 0 ∨
      ascentRoot n hthree vertex hneOne hneTop = simpleRoot n hthree 1) ∧
      length n hthree ((ascentRoot n hthree vertex hneOne hneTop).reflection * vertex) =
        length n hthree vertex + 1 :=
  (Classical.choose_spec (unique_root_ascent n hthree vertex hneOne hneTop)).1

/-- Schubert splines recurse downward from the positive-form top by divided differences. -/
def construct (vertex : DihedralGroup n) :
    HomogeneousAt (HessenbergIdeal.full n hthree) vertex :=
  if hidentity : vertex = 1 then by
    subst vertex
    exact identity n hthree
  else if htop : vertex = longestElement n hthree then by
    subst vertex
    exact topCertificate n hthree
  else
    let alpha := ascentRoot n hthree vertex hidentity htop
    let hstep := ascentRoot_spec n hthree vertex hidentity htop
    HomogeneousAt.differenceStep alpha hstep.1 hstep.2
      (construct (alpha.reflection * vertex))
      (fun current _ => full_edge alpha current)
      (by
        change (RootSubset.full n).length (alpha.reflection * vertex) =
          (RootSubset.full n).length vertex + 1
        rw [RootSubset.length_full n hthree, RootSubset.length_full n hthree]
        exact hstep.2)
termination_by n - length n hthree vertex
decreasing_by
  have _hstep := (ascentRoot_spec n hthree vertex hidentity htop).2
  have hbound := length_le_polygon_parameter n hthree
    ((ascentRoot n hthree vertex hidentity htop).reflection * vertex)
  omega

/-- The geometric Schubert spline is the value of its homogeneous upper-support certificate. -/
def spline (vertex : DihedralGroup n) : (HessenbergIdeal.full n hthree).toRootSubset.Spline :=
  (construct n hthree vertex).value

/-- The identity Schubert spline is the constant one spline. -/
theorem spline_one : spline n hthree 1 = 1 := by
  simp [spline, construct, identity]

/-- The longest-element Schubert spline is the positive-form top spline. -/
theorem spline_top : spline n hthree (longestElement n hthree) = top n hthree := by
  have hne : longestElement n hthree ≠ 1 := by
    intro heq
    have hlength := (length_eq_longest n hthree _).mpr rfl
    rw [heq, Schubert.Dihedral.length_one] at hlength
    omega
  simp [spline, construct, hne, topCertificate]

/-- At every nonendpoint the exact displayed simple-root divided-difference recursion holds. -/
theorem spline_step (vertex : DihedralGroup n) (hneOne : vertex ≠ 1)
    (hneTop : vertex ≠ longestElement n hthree) :
    let alpha := ascentRoot n hthree vertex hneOne hneTop
    spline n hthree vertex = difference (spline n hthree (alpha.reflection * vertex)) alpha := by
  dsimp only
  unfold spline
  rw [construct]
  simp only [dite_eq_right hneOne, dite_eq_right hneTop]
  rfl

/-- Schubert splines are homogeneous of the canonical vertex length. -/
theorem homogeneous (vertex : DihedralGroup n) :
    spline n hthree vertex ∈ (RootSubset.full n).piece (length n hthree vertex) := by
  rw [← RootSubset.length_full n hthree vertex]
  exact (construct n hthree vertex).homogeneous

/-- Each Schubert spline is supported in the Bruhat upper ideal of its vertex. -/
theorem support (vertex current : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree vertex current) :
    (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current = 0 :=
  (construct n hthree vertex).support current hnot

/-- Every Schubert spline has nonzero diagonal. -/
theorem diagonal (vertex : DihedralGroup n) :
    (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 :=
  (construct n hthree vertex).diagonal

end Schubert.DihedralSplines.SchubertSpline
