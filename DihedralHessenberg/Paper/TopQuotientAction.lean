import DihedralHessenberg.Paper.PaperDividedDifference
import DihedralHessenberg.Paper.PaperTop
import DihedralHessenberg.Paper.HessenbergTopEdge
import DihedralHessenberg.Paper.PaperQuotientAction
import DihedralHessenberg.Dihedral.LongestReversal
import DihedralHessenberg.Dihedral.RootNormal
import DihedralHessenberg.Dihedral.RootNoLoops
import DihedralHessenberg.Splines.PolynomialAugmentation

/-! # Simple reflections on the top quotient classes -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every nonzero top vertex admits the selected left edge of any simple root. -/
theorem top_admissible (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (vertex : DihedralGroup n)
    (hvalue : (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) :
    (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges := by
  have hvertex : vertex = longestElement n hthree := by
    by_contra hnot
    exact hvalue (by rw [ideal.topSpline_apply, ite_eq_right hnot])
  subst vertex
  have hsimpleLength : length n hthree alpha.reflection = 1 := by
    rcases hsimple with rfl | rfl <;> rw [simpleRoot_reflection, length_simpleReflection]
  have hinverse : (longestElement n hthree)⁻¹ = longestElement n hthree :=
    alternatingWord_top_inv n hthree
  have hlength : length n hthree (alpha.reflection * longestElement n hthree) = n - 1 := by
    rw [← length_inv n hthree (_ * _), mul_inv_rev, hinverse, alpha.reflection_inv,
      length_longest_mul, hsimpleLength]
  have htop : alpha.reflection * (alpha.reflection * longestElement n hthree) =
      longestElement n hthree := by rw [← mul_assoc, alpha.reflection_square, one_mul]
  have hascent : length n hthree (alpha.reflection * (alpha.reflection *
      longestElement n hthree)) =
      length n hthree (alpha.reflection * longestElement n hthree) + 1 := by
    rw [htop, hlength, (length_eq_longest n hthree _).mpr rfl]
    omega
  obtain ⟨gamma, hgamma, hendpoint⟩ := ideal.edge_to_top alpha hsimple
    (alpha.reflection * longestElement n hthree) hascent htop
  refine ⟨gamma, hgamma, ?_⟩
  change alpha.reflection * longestElement n hthree = longestElement n hthree * gamma.reflection
  change alpha.reflection * (alpha.reflection * longestElement n hthree) =
    (alpha.reflection * longestElement n hthree) * gamma.reflection at hendpoint
  have heq : longestElement n hthree =
      (alpha.reflection * longestElement n hthree) * gamma.reflection :=
    htop.symm.trans hendpoint
  calc
    _ = ((alpha.reflection * longestElement n hthree) * gamma.reflection) *
      gamma.reflection := by rw [mul_assoc, gamma.reflection_square, mul_one]
    _ = _ := (congrArg (fun value => value * gamma.reflection) heq).symm

/-- The simple top numerator is a constant-root-form multiple of its divided difference. -/
theorem top_numerator (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ideal.topSpline - ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline =
      ideal.toRootSubset.constantHom hthree alpha.form *
        ideal.dividedDifference ideal.topSpline alpha (ideal.top_admissible alpha hsimple) := by
  apply Subtype.ext
  funext vertex
  exact (ideal.dividedDifference_mul ideal.topSpline alpha
    (ideal.top_admissible alpha hsimple) vertex).symm

namespace Left
/-- A simple reflection fixes the left top quotient class. -/
theorem top_simple_fixed (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    RootSubset.Left.dotEquiv ideal.toRootSubset hthree alpha.reflection
      (RootSubset.Left.quotientMap ideal.toRootSubset hthree ideal.topSpline) =
      RootSubset.Left.quotientMap ideal.toRootSubset hthree ideal.topSpline := by
  rw [RootSubset.Left.dot_map]
  apply sub_eq_zero.mp
  rw [← map_sub]
  have hzero : RootSubset.Left.quotientMap ideal.toRootSubset hthree
      (ideal.topSpline - ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline) = 0 := by
    apply (RootSubset.Left.map_zero_iff _ _ _).mpr
    rw [ideal.top_numerator alpha hsimple]
    apply Ideal.mul_mem_right
    apply Ideal.mem_map_of_mem (ideal.toRootSubset.constantHom hthree).toRingHom
    apply (PolynomialAugmentation.mem_iff_constantCoeff_zero alpha.form).mpr
    simp [PositiveRoot.form, linearPolynomial]
  rw [map_sub] at hzero
  exact (sub_eq_zero.mpr (sub_eq_zero.mp hzero).symm)
end Left

/-- The orbit-normal factor turns the top divided difference numerator into the top sum. -/
theorem top_orbit_numerator (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ideal.topSpline + ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline =
      ideal.toRootSubset.orbitHom hthree
        (polynomialAction n (longestElement n hthree)⁻¹ alpha.form) *
        ideal.dividedDifference ideal.topSpline alpha (ideal.top_admissible alpha hsimple) := by
  apply Subtype.ext
  funext vertex
  have hseparate : alpha.reflection * longestElement n hthree ≠ longestElement n hthree := by
    intro heq
    apply alpha.reflection_ne_one
    exact mul_right_cancel (heq.trans (one_mul _).symm)
  have hnumerator := ideal.dividedDifference_mul ideal.topSpline alpha
    (ideal.top_admissible alpha hsimple) vertex
  change (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) vertex +
    (ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline :
      DihedralGroup n → CoordinatePolynomial) vertex =
    polynomialAction n vertex (polynomialAction n (longestElement n hthree)⁻¹ alpha.form) *
      (ideal.dividedDifference ideal.topSpline alpha (ideal.top_admissible alpha hsimple) :
        DihedralGroup n → CoordinatePolynomial) vertex
  by_cases htop : vertex = longestElement n hthree
  · subst vertex
    have hdot : (ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline :
        DihedralGroup n → CoordinatePolynomial) (longestElement n hthree) = 0 := by
      rw [RootSubset.dot_apply, alpha.reflection_inv, ideal.topSpline_apply,
        ite_eq_right hseparate, map_zero]
    rw [hdot, sub_zero] at hnumerator
    rw [hdot, add_zero, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact hnumerator.symm
  · by_cases hother : vertex = alpha.reflection * longestElement n hthree
    · subst vertex
      have hzero : (ideal.topSpline : DihedralGroup n → CoordinatePolynomial)
          (alpha.reflection * longestElement n hthree) = 0 := by
        rw [ideal.topSpline_apply, ite_eq_right hseparate]
      rw [hzero, zero_sub] at hnumerator
      rw [hzero, zero_add, ← AlgEquiv.mul_apply, ← map_mul, mul_assoc,
        mul_inv_cancel, mul_one, alpha.reflection_form, neg_mul]
      simpa only [neg_neg] using (congrArg Neg.neg hnumerator).symm
    · have hzero : (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
        rw [ideal.topSpline_apply, ite_eq_right htop]
      have hreflected : alpha.reflection * vertex ≠ longestElement n hthree := by
        intro heq
        apply hother
        calc
          vertex = alpha.reflection * (alpha.reflection * vertex) := by
            rw [← mul_assoc, alpha.reflection_square, one_mul]
          _ = _ := congrArg (fun value => alpha.reflection * value) heq
      have hdot : (ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline :
          DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
        rw [RootSubset.dot_apply, alpha.reflection_inv, ideal.topSpline_apply,
          ite_eq_right hreflected, map_zero]
      rw [hzero, hdot, sub_zero] at hnumerator
      have hdd := (mul_eq_zero.mp hnumerator).resolve_left alpha.form_ne_zero
      rw [hzero, hdot, hdd, add_zero, mul_zero]

namespace Right
/-- A simple reflection negates the right top quotient class. -/
theorem top_simple_negated (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    RootSubset.Right.dotEquiv ideal.toRootSubset hthree alpha.reflection
      (RootSubset.Right.quotientMap ideal.toRootSubset hthree ideal.topSpline) =
      -RootSubset.Right.quotientMap ideal.toRootSubset hthree ideal.topSpline := by
  rw [RootSubset.Right.dot_map]
  apply eq_neg_of_add_eq_zero_left
  have hzero : RootSubset.Right.quotientMap ideal.toRootSubset hthree
      (ideal.topSpline + ideal.toRootSubset.dot hthree alpha.reflection ideal.topSpline) = 0 := by
    apply (RootSubset.Right.map_zero_iff _ _ _).mpr
    rw [ideal.top_orbit_numerator alpha hsimple]
    apply Ideal.mul_mem_right
    apply Ideal.mem_map_of_mem (ideal.toRootSubset.orbitHom hthree).toRingHom
    apply (PolynomialAugmentation.mem_iff_constantCoeff_zero _).mpr
    have hh : (polynomialAction n (longestElement n hthree)⁻¹ alpha.form).IsHomogeneous 1 := by
      apply polynomialAction_isHomogeneous
      rw [PositiveRoot.form_index]
      exact rootPolynomial_isHomogeneous n alpha.index
    by_contra hnonzero
    have hdegree := hh hnonzero
    simp at hdegree
  simpa only [map_add, add_comm] using hzero
end Right

end Schubert.DihedralSplines.HessenbergIdeal
