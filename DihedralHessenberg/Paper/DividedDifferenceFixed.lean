import DihedralHessenberg.Paper.PaperDividedDifference
import DihedralHessenberg.Dihedral.RootNormal
import DihedralHessenberg.Paper.FlowupEquations

/-! # Reflection invariance of geometric divided differences -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every admissible divided difference is fixed by reflection in its normal root. -/
theorem dividedDifference_fixed (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ideal.toRootSubset.dot hthree alpha.reflection (ideal.dividedDifference value alpha hedges) =
      ideal.dividedDifference value alpha hedges := by
  have hnumerator : ideal.toRootSubset.constantHom hthree alpha.form *
      ideal.dividedDifference value alpha hedges =
      value - ideal.toRootSubset.dot hthree alpha.reflection value := by
    apply Subtype.ext
    funext vertex
    exact ideal.dividedDifference_mul value alpha hedges vertex
  have hnormal : ideal.toRootSubset.dot hthree alpha.reflection
      (ideal.toRootSubset.constantHom hthree alpha.form) =
      -(ideal.toRootSubset.constantHom hthree alpha.form) := by
    apply Subtype.ext
    funext vertex
    exact alpha.reflection_form
  have htranslated := congrArg
    (ideal.toRootSubset.dotEquiv hthree alpha.reflection) hnumerator
  rw [map_mul, map_sub] at htranslated
  simp only [RootSubset.dotEquiv_apply, hnormal] at htranslated
  rw [← RootSubset.dot_mul, alpha.reflection_square, RootSubset.dot_one] at htranslated
  apply Subtype.ext
  funext vertex
  have hpoint := congrArg (fun spline : ideal.toRootSubset.Spline =>
    (spline : DihedralGroup n → CoordinatePolynomial) vertex) htranslated
  change (-alpha.form) *
    (ideal.toRootSubset.dot hthree alpha.reflection
      (ideal.dividedDifference value alpha hedges) :
      DihedralGroup n → CoordinatePolynomial) vertex =
    (ideal.toRootSubset.dot hthree alpha.reflection value :
      DihedralGroup n → CoordinatePolynomial) vertex -
      (value : DihedralGroup n → CoordinatePolynomial) vertex at hpoint
  rw [neg_mul] at hpoint
  have hnum := ideal.dividedDifference_mul value alpha hedges vertex
  apply mul_left_cancel₀ alpha.form_ne_zero
  apply neg_injective
  rw [hpoint, hnum, neg_sub]
end Schubert.DihedralSplines.HessenbergIdeal

namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A selected upper-half flow-up is fixed by its simple ascent reflection. -/
theorem high_fixed (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ideal.toRootSubset.dot hthree alpha.reflection (spline ideal vertex) =
      spline ideal vertex := by
  have hneOne : vertex ≠ 1 := by
    intro heq
    rw [heq, length_one] at hhalf
    omega
  have hneTop : vertex ≠ longestElement n hthree := by
    intro heq
    have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
    have hlength := (length_eq_longest n hthree vertex).mpr heq
    omega
  rw [spline_high ideal vertex hneOne hneTop alpha hsimple hascent hedge hhalf]
  exact ideal.dividedDifference_fixed _ alpha _
end Schubert.DihedralSplines.FlowupSpline
