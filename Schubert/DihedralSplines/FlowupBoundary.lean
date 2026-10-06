import Schubert.DihedralSplines.BoundaryFormDot
import Schubert.DihedralSplines.FlowupEquations

/-! # Explicit boundary forms for the recursive flow-up family -/

noncomputable section

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The longest recursive spline has a boundary form on its singleton upper ideal. -/
def topForm : BoundaryForm ideal (longestElement n hthree)
    (spline ideal (longestElement n hthree)) := by
  have hlength : length n hthree (longestElement n hthree) = n :=
    (length_eq_longest n hthree _).mpr rfl
  let upper : HessenbergIdeal.Upper ideal := ⟨longestElement n hthree,
    by simp [hlength], by rw [ideal.length_top, hlength]; simp⟩
  exact BoundaryForm.ofUpper upper _ (homogeneous ideal _) (support ideal _) (diagonal ideal _)

/-- Every selected upper-half recursive spline has the exact nonzero boundary form. -/
def highForm (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    BoundaryForm ideal vertex (spline ideal vertex) :=
  BoundaryForm.ofUpper (HessenbergIdeal.Upper.ofAscent ideal alpha hsimple vertex
    hascent hhalf hedge) _ (homogeneous ideal _) (support ideal _) (diagonal ideal _)

/-- Each recursive vector is a Schubert restriction or has the displayed boundary form. -/
theorem shape (vertex : DihedralGroup n) :
    spline ideal vertex = ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree vertex) ∨
      Nonempty (BoundaryForm ideal vertex (spline ideal vertex)) := by
  classical
  generalize hmeasure : n - length n hthree vertex = measure
  induction measure using Nat.strong_induction_on generalizing vertex with
  | h measure ih =>
    by_cases hidentity : vertex = 1
    · subst vertex
      left
      rw [spline_one, SchubertSpline.spline_one]
      rfl
    by_cases htop : vertex = longestElement n hthree
    · subst vertex
      exact Or.inr ⟨topForm ideal⟩
    let alpha := SchubertSpline.ascentRoot n hthree vertex hidentity htop
    have hsimple := (SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop).1
    have hascent := (SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop).2
    change (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) at hsimple
    change length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1 at hascent
    by_cases hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges
    · by_cases hhalf : 2 * length n hthree vertex + 1 ≤ n
      · exact Or.inl (spline_low ideal vertex hidentity htop alpha hsimple hascent hedge hhalf)
      · exact Or.inr ⟨highForm ideal vertex alpha hsimple hascent (by omega) hedge⟩
    · have hup : BruhatLE n hthree vertex (alpha.reflection * vertex) :=
        bruhatLE_of_length_lt n hthree (by omega)
      have hne : vertex ≠ alpha.reflection * vertex := by
        intro heq
        have hlen := congrArg (length n hthree) heq
        omega
      have hdegree : ideal.toRootSubset.length (alpha.reflection * vertex) =
          ideal.toRootSubset.length vertex := by
        change (ideal.toRootSubset.inversions (alpha.reflection * vertex)).ncard =
          (ideal.toRootSubset.inversions vertex).ncard
        rw [ideal.inversions_no_edge alpha hsimple vertex hup hne hedge]
      have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
      have hless : n - length n hthree (alpha.reflection * vertex) < measure := by omega
      obtain hschubert | hlocalized := ih _ hless (alpha.reflection * vertex) rfl
      · have hdegreeSchubert := congrArg ideal.toRootSubset.degree hschubert
        rw [degree] at hdegreeSchubert
        have hrestricted : ideal.toRootSubset.degree
            (ideal.toRootSubset.restrictFull
              (SchubertSpline.spline n hthree (alpha.reflection * vertex))) =
                length n hthree (alpha.reflection * vertex) := by
          change (RootSubset.full n).degree
            (SchubertSpline.spline n hthree (alpha.reflection * vertex)) = _
          exact ((SchubertSpline.construct n hthree (alpha.reflection * vertex)).degree_eq).trans
            (RootSubset.length_full n hthree (alpha.reflection * vertex))
        rw [hrestricted, hdegree] at hdegreeSchubert
        have hdegreeBound : ideal.toRootSubset.length vertex ≤ length n hthree vertex := by
          rw [ideal.length_indexed]
          exact ideal.indexed.length_le_coxeter_length vertex
        omega
      · right
        let form := Classical.choice hlocalized
        have houtput := spline_no_edge ideal vertex hidentity htop alpha hsimple hascent hedge
        have hreturn : alpha.reflection * (alpha.reflection * vertex) = vertex := by
          rw [← mul_assoc, alpha.reflection_square, one_mul]
        have translated := form.ofDot alpha.reflection vertex hreturn (by
          intro current hnot
          rw [← houtput]
          exact support ideal vertex current hnot)
        rw [← houtput] at translated
        exact ⟨translated⟩

end Schubert.DihedralSplines.FlowupSpline
