import DihedralHessenberg.Paper.FlowupEquations
import DihedralHessenberg.Paper.GeometricQuotientBasis
import DihedralHessenberg.Paper.PaperQuotientAction

/-! # Single-vertex classes under dot translation -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Polynomial translation takes the incident product to the translated incident product. -/
theorem labelProduct_action (translate vertex : DihedralGroup n) :
    polynomialAction n translate (ideal.labelProduct vertex) =
      ideal.labelProduct (translate * vertex) := by
  rw [ideal.labelProduct_backend, ideal.labelProduct_backend, map_prod]
  apply Finset.prod_congr rfl
  intro index _
  have haction := congrArg (fun action : CoordinatePolynomial ≃ₐ[ℂ] CoordinatePolynomial =>
    action (rootPolynomial n index)) ((polynomialAction n).map_mul translate vertex)
  exact haction.symm

/-- The single-vertex splines translate without an additional scalar. -/
theorem singleSpline_dot (translate vertex : DihedralGroup n) :
    ideal.toRootSubset.dot hthree translate (ideal.singleSpline vertex) =
      ideal.singleSpline (translate * vertex) := by
  apply Subtype.ext
  funext current
  rw [RootSubset.dot_apply, ideal.singleSpline_apply, ideal.singleSpline_apply]
  by_cases heq : current = translate * vertex
  · subst current
    simp only [inv_mul_cancel_left, ite_true]
    exact ideal.labelProduct_action translate vertex
  · have hnot : translate⁻¹ * current ≠ vertex := by
      intro h
      apply heq
      calc
        current = translate * (translate⁻¹ * current) := (mul_inv_cancel_left _ _).symm
        _ = translate * vertex := congrArg (fun value => translate * value) h
    rw [ite_eq_right hnot, ite_eq_right heq, map_zero]

namespace Left

/-- The top singleton retains its nonzero left quotient basis class. -/
theorem top_class_ne_zero :
    RootSubset.Left.quotientMap ideal.toRootSubset hthree ideal.topSpline ≠ 0 := by
  let := ideal.toRootSubset.leftAlgebra hthree
  have hnonzero := (RootSubset.Left.quotientBasis ideal.toRootSubset hthree
    (FlowupSpline.Left.basis ideal)).ne_zero (longestElement n hthree)
  rw [RootSubset.Left.quotientBasis_apply, FlowupSpline.Left.basis_apply,
    FlowupSpline.spline_top] at hnonzero
  exact hnonzero

/-- Every singleton has nonzero left quotient class. -/
theorem single_class_ne_zero (vertex : DihedralGroup n) :
    RootSubset.Left.quotientMap ideal.toRootSubset hthree (ideal.singleSpline vertex) ≠ 0 := by
  have htranslate := ideal.singleSpline_dot
    (vertex * (longestElement n hthree)⁻¹) (longestElement n hthree)
  rw [inv_mul_cancel_right] at htranslate
  rw [← htranslate, ← RootSubset.Left.dot_map]
  exact fun h => top_class_ne_zero ideal
    ((RootSubset.Left.dotEquiv ideal.toRootSubset hthree _).injective
      (h.trans (map_zero _).symm))

end Left
namespace Right

/-- The top singleton retains its nonzero right quotient basis class. -/
theorem top_class_ne_zero :
    RootSubset.Right.quotientMap ideal.toRootSubset hthree ideal.topSpline ≠ 0 := by
  let := ideal.toRootSubset.rightAlgebra hthree
  have hnonzero := (RootSubset.Right.quotientBasis ideal.toRootSubset hthree
    (FlowupSpline.Right.basis ideal)).ne_zero (longestElement n hthree)
  rw [RootSubset.Right.quotientBasis_apply, FlowupSpline.Right.basis_apply,
    FlowupSpline.spline_top] at hnonzero
  exact hnonzero

/-- Every singleton has nonzero right quotient class. -/
theorem single_class_ne_zero (vertex : DihedralGroup n) :
    RootSubset.Right.quotientMap ideal.toRootSubset hthree (ideal.singleSpline vertex) ≠ 0 := by
  have htranslate := ideal.singleSpline_dot
    (vertex * (longestElement n hthree)⁻¹) (longestElement n hthree)
  rw [inv_mul_cancel_right] at htranslate
  rw [← htranslate, ← RootSubset.Right.dot_map]
  exact fun h => top_class_ne_zero ideal
    ((RootSubset.Right.dotEquiv ideal.toRootSubset hthree _).injective
      (h.trans (map_zero _).symm))

end Right
end Schubert.DihedralSplines.HessenbergIdeal
