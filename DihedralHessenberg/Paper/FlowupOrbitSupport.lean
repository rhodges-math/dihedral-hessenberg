import DihedralHessenberg.Paper.FlowupOrbitStabilizer

/-! # Support distinguishes the upper-half spline orbit -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The support set has the same stabilizer as the upper-half spline. -/
theorem high_support_stabilizer (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (element : DihedralGroup n) :
    Function.support (ideal.toRootSubset.dot hthree element (spline ideal vertex) :
        DihedralGroup n → CoordinatePolynomial) =
      Function.support (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) ↔
      element = 1 ∨ element = alpha.reflection := by
  obtain ⟨block, _, _, hvertices⟩ := ideal.ascent_block alpha hsimple vertex hascent hhalf hedge
  have hsupport : Function.support (spline ideal vertex :
      DihedralGroup n → CoordinatePolynomial) = (block.vertices : Set (DihedralGroup n)) := by
    ext current
    rw [Function.mem_support, hvertices]
    exact support_high ideal vertex alpha hsimple hascent hhalf hedge current
  have hterminal : alpha.reflection = block.base * block.gamma.reflection * block.base⁻¹ := by
    have hsets := congrArg (fun value : ideal.toRootSubset.Spline =>
      Function.support (value : DihedralGroup n → CoordinatePolynomial))
      (high_fixed ideal vertex alpha hsimple hascent hhalf hedge)
    rw [ideal.toRootSubset.dot_support_set hthree, hsupport] at hsets
    exact ((block.image_stabilizer alpha.reflection).mp hsets).resolve_left alpha.reflection_ne_one
  rw [ideal.toRootSubset.dot_support_set hthree, hsupport, block.image_stabilizer, ← hterminal]

/-- Equality of supports is equivalent to equality of orbit splines. -/
theorem high_support_eq (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (first second : DihedralGroup n) :
    Function.support (ideal.toRootSubset.dot hthree first (spline ideal vertex) :
        DihedralGroup n → CoordinatePolynomial) =
      Function.support (ideal.toRootSubset.dot hthree second (spline ideal vertex) :
        DihedralGroup n → CoordinatePolynomial) ↔
      ideal.toRootSubset.dot hthree first (spline ideal vertex) =
        ideal.toRootSubset.dot hthree second (spline ideal vertex) := by
  constructor
  · intro hsets
    have hinverse := congrArg
      (fun support : Set (DihedralGroup n) => (fun current => second⁻¹ * current) '' support) hsets
    rw [ideal.toRootSubset.dot_support_set hthree,
      ideal.toRootSubset.dot_support_set hthree] at hinverse
    simp only [Set.image_image, ← mul_assoc, inv_mul_cancel,
      one_mul, Set.image_id'] at hinverse
    have hcondition := (high_support_stabilizer ideal vertex alpha hsimple hascent hhalf hedge
      (second⁻¹ * first)).mp (by
        rw [ideal.toRootSubset.dot_support_set hthree]
        exact hinverse)
    have hfixed := (high_stabilizer ideal vertex alpha hsimple hascent hhalf hedge
      (second⁻¹ * first)).mpr hcondition
    have htranslated := congrArg (ideal.toRootSubset.dot hthree second) hfixed
    simpa only [← ideal.toRootSubset.dot_mul hthree, mul_inv_cancel_left] using htranslated
  · intro heq
    exact congrArg (fun value : ideal.toRootSubset.Spline =>
      Function.support (value : DihedralGroup n → CoordinatePolynomial)) heq
end Schubert.DihedralSplines.FlowupSpline
