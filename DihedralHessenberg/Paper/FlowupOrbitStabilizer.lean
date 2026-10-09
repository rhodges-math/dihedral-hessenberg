import DihedralHessenberg.Paper.BoundaryTranslation
import DihedralHessenberg.Paper.BlockStabilizer
import DihedralHessenberg.Paper.FlowupBlock
import DihedralHessenberg.Paper.DividedDifferenceFixed
import DihedralHessenberg.Dihedral.RootNoLoops

/-! # Support sets under the spline dot action -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
variable {n : ℕ} [NeZero n] (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Dot translation left-translates the nonzero support set. -/
theorem dot_support_set (element : DihedralGroup n) (value : selected.Spline) :
    Function.support (selected.dot hthree element value :
        DihedralGroup n → CoordinatePolynomial) =
      (fun vertex => element * vertex) '' Function.support
        (value : DihedralGroup n → CoordinatePolynomial) := by
  ext current
  simp only [Function.mem_support, Set.mem_image]
  constructor
  · intro hcurrent
    refine ⟨element⁻¹ * current, ?_, mul_inv_cancel_left _ _⟩
    apply (selected.dot_support hthree element (element⁻¹ * current) value).mp
    simpa only [mul_inv_cancel_left] using hcurrent
  · rintro ⟨original, horiginal, rfl⟩
    exact (selected.dot_support hthree element original value).mpr horiginal
end Schubert.Dihedral.RootSubset

namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A selected upper-half spline has exactly its simple-ascent stabilizer. -/
theorem high_stabilizer (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (element : DihedralGroup n) :
    ideal.toRootSubset.dot hthree element (spline ideal vertex) = spline ideal vertex ↔
      element = 1 ∨ element = alpha.reflection := by
  obtain ⟨block, _, _, hvertices⟩ := ideal.ascent_block alpha hsimple vertex hascent hhalf hedge
  have hsupport : Function.support (spline ideal vertex :
      DihedralGroup n → CoordinatePolynomial) = (block.vertices : Set (DihedralGroup n)) := by
    ext current
    rw [Function.mem_support, hvertices]
    exact support_high ideal vertex alpha hsimple hascent hhalf hedge current
  have hcondition : ∀ translate,
      ideal.toRootSubset.dot hthree translate (spline ideal vertex) = spline ideal vertex →
      translate = 1 ∨ translate = block.base * block.gamma.reflection * block.base⁻¹ := by
    intro translate hfixed
    have hsets := congrArg (fun value : ideal.toRootSubset.Spline =>
      Function.support (value : DihedralGroup n → CoordinatePolynomial)) hfixed
    rw [ideal.toRootSubset.dot_support_set hthree, hsupport] at hsets
    exact (block.image_stabilizer translate).mp hsets
  have hterminal : alpha.reflection = block.base * block.gamma.reflection * block.base⁻¹ :=
    (hcondition alpha.reflection
      (high_fixed ideal vertex alpha hsimple hascent hhalf hedge)).resolve_left
      alpha.reflection_ne_one
  constructor
  · intro hfixed
    simpa only [← hterminal] using hcondition element hfixed
  · rintro (rfl | rfl)
    · exact ideal.toRootSubset.dot_one hthree _
    · exact high_fixed ideal vertex alpha hsimple hascent hhalf hedge
end Schubert.DihedralSplines.FlowupSpline
