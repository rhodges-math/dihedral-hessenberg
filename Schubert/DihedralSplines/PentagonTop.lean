import Schubert.DihedralSplines.PentagonDegree
import Schubert.Dihedral.RootObjectAction

/-! # The pentagon top generator -/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral

private theorem negative_image (coordinate : ZMod 5) (index image : Fin 5)
    (hangle : (5 - angularIndex index - 2 * coordinate.val : ℤ) % 10 =
      angularIndex image + 5) :
    realAction 5 (.sr coordinate) (positiveRoot 5 index) = -positiveRoot 5 image := by
  apply complexify_injective
  rw [realAction_complexify 5 _ _ (Or.inl ⟨index, rfl⟩)]
  change vectorOperator 5 (.sr coordinate) (complexPositiveRoot 5 index) = _
  rw [vectorOperator_sr_complexPositiveRoot]
  apply congrArg complexify
  rw [unitRootAt_int_eq_emod]
  norm_num only [Nat.cast_ofNat, Int.reduceMul]
  rw [hangle, positiveRoot, rootAngle_eq_angularIndex,
    ← unitRootAt_add_pi]
  congr 1
  push_cast
  ring

private theorem top_form (index image : Fin 5)
    (hangle : (5 - angularIndex index - 6 : ℤ) % 10 = angularIndex image + 5) :
    polynomialAction 5 (vertices 9) (rootPolynomial 5 index) = -rootPolynomial 5 image := by
  change polynomialAction 5 (vertices 9) (positiveRootEquiv 5 index).form = _
  rw [PositiveRoot.action_form]
  have hroot : realAction 5 (vertices 9) (positiveRoot 5 index) = -positiveRoot 5 image := by
    norm_num only [vertices, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
      DihedralGroup.r_zero, pow_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    change realAction 5 (.sr 3) (positiveRoot 5 index) = -positiveRoot 5 image
    exact negative_image _ _ _ hangle
  change linearPolynomial (complexify (realAction 5 (vertices 9) (positiveRoot 5 index))) = _
  rw [hroot]
  simp only [rootPolynomial, complexPositiveRoot, complexify, Pi.neg_apply,
    Complex.ofReal_neg, linearPolynomial, map_neg]
  ring

/-- The top spline has the displayed negative product and singleton support. -/
theorem top_values (current : DihedralGroup 5) :
    (ideal.topSpline : DihedralGroup 5 → CoordinatePolynomial) current =
      if current = vertices 9 then
        -(positiveRootEquiv 5 0).form * (positiveRootEquiv 5 1).form *
          (positiveRootEquiv 5 3).form else 0 := by
  change (ideal.singleSpline (longestElement 5 (by decide)) :
    DihedralGroup 5 → CoordinatePolynomial) current = _
  rw [ideal.singleSpline_apply, ← last_vertex]
  congr 1
  rw [ideal.labelProduct_backend, indexed_roots]
  have h0 := top_form 0 1 (by decide)
  have h1 := top_form 1 0 (by decide)
  have h2 := top_form 2 3 (by decide)
  norm_num [Finset.prod_insert]
  rw [h0, h1, h2]
  ring

/-- The top generator has its homogeneous upper-spline certificate. -/
def top : HomogeneousAt ideal (vertices 9) :=
  last_vertex.symm ▸ FlowupSpline.topCertificate ideal

private theorem cast_value {first second : DihedralGroup 5} (heq : first = second)
    (value : HomogeneousAt ideal first) : (heq ▸ value).value = value.value := by
  cases heq
  rfl

/-- The certificate retains the transformed-product top spline. -/
theorem top_value : top.value = ideal.topSpline := by
  exact cast_value last_vertex.symm (FlowupSpline.topCertificate ideal)

end Schubert.DihedralSplines.Pentagon
