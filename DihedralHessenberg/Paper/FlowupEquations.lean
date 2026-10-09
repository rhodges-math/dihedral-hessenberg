import DihedralHessenberg.Paper.FlowupBasis

/-! # Exact recursion equations for the geometric flow-up functions -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

namespace SchubertSpline

/-- Every simple ascent equals the uniquely chosen ascent vector. -/
theorem ascentRoot_eq {n : ℕ} (hthree : 3 ≤ n) (vertex : DihedralGroup n)
    (hneOne : vertex ≠ 1) (hneTop : vertex ≠ longestElement n hthree)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1) :
    ascentRoot n hthree vertex hneOne hneTop = alpha :=
  ((Classical.choose_spec (unique_root_ascent n hthree vertex hneOne hneTop)).2
    alpha ⟨hsimple, hascent⟩).symm

end SchubertSpline

namespace FlowupSpline

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The recursive identity flow-up spline is the unit function. -/
theorem spline_one : spline ideal 1 = 1 := by
  unfold spline
  rw [construct]
  simp only
  rfl

/-- The recursive longest-element spline is the exact transformed H-top product. -/
theorem spline_top : spline ideal (longestElement n hthree) = ideal.topSpline := by
  have hne : longestElement n hthree ≠ 1 := by
    intro heq
    have hlength := (length_eq_longest n hthree (longestElement n hthree)).2 rfl
    rw [heq, length_one] at hlength
    omega
  unfold spline
  rw [construct]
  simp only [dite_eq_right hne]
  rfl

variable (vertex : DihedralGroup n) (hneOne : vertex ≠ 1)
variable (hneTop : vertex ≠ longestElement n hthree) (alpha : PositiveRoot n)
variable (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
variable (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)

include hneOne hneTop hsimple hascent in
/-- A selected lower-half ascent uses the restriction of the full Schubert spline. -/
theorem spline_low (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hhalf : 2 * length n hthree vertex + 1 ≤ n) :
    spline ideal vertex = ideal.toRootSubset.restrictFull
      (SchubertSpline.spline n hthree vertex) := by
  have hchoice := SchubertSpline.ascentRoot_eq hthree vertex hneOne hneTop alpha hsimple hascent
  subst alpha
  unfold spline
  rw [construct]
  simp only [dite_eq_right hneOne, dite_eq_right hneTop,
    dite_eq_left hedge, dite_eq_left hhalf]
  rfl

include hsimple hascent in
/-- Every nonzero tail value in an upper-half selected ascent has the required edge. -/
theorem step_admissible
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hhalf : n < 2 * length n hthree vertex + 1) :
    ∀ current,
      (spline ideal (alpha.reflection * vertex) : DihedralGroup n → CoordinatePolynomial)
        current ≠ 0 → (current, alpha.reflection * current) ∈ ideal.toRootSubset.edges := by
  intro current hnonzero
  apply ideal.edge_above alpha hsimple vertex hascent hhalf hedge current
  by_contra hnot
  exact hnonzero (support ideal (alpha.reflection * vertex) current hnot)

include hneOne hneTop in
/-- A selected upper-half ascent uses exactly the root divided difference of its tail. -/
theorem spline_high (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hhalf : n < 2 * length n hthree vertex + 1) :
    spline ideal vertex = ideal.dividedDifference (spline ideal (alpha.reflection * vertex))
      alpha (step_admissible ideal vertex alpha hsimple hascent hedge hhalf) := by
  have hchoice := SchubertSpline.ascentRoot_eq hthree vertex hneOne hneTop alpha hsimple hascent
  subst alpha
  unfold spline
  rw [construct]
  simp only [dite_eq_right hneOne, dite_eq_right hneTop,
    dite_eq_left hedge, dite_eq_right (Nat.not_le_of_lt hhalf)]
  rfl

include hneOne hneTop hsimple hascent in
/-- An absent ascent edge uses the exact reflection dot translation of the tail. -/
theorem spline_no_edge
    (hedge : (vertex, alpha.reflection * vertex) ∉ ideal.toRootSubset.edges) :
    spline ideal vertex =
      ideal.toRootSubset.dot hthree alpha.reflection
        (spline ideal (alpha.reflection * vertex)) := by
  have hchoice := SchubertSpline.ascentRoot_eq hthree vertex hneOne hneTop alpha hsimple hascent
  subst alpha
  unfold spline
  rw [construct]
  simp only [dite_eq_right hneOne, dite_eq_right hneTop, dite_eq_right hedge]
  rfl

end FlowupSpline

end Schubert.DihedralSplines
