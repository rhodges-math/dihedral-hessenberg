import Schubert.DihedralSplines.SingletonNormalization

/-! # Nonzero matched products in the geometric quotients -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The upward/downward diagonal product has nonzero left quotient class. -/
theorem paired_product_ne_zero (vertex : DihedralGroup n) :
    RootSubset.Left.quotientMap ideal.toRootSubset hthree
      (spline ideal vertex * opposite ideal vertex) ≠ 0 := by
  obtain ⟨scalar, hscalar, heq⟩ := opposite_product_singleton ideal vertex
  rw [heq]
  change (RootSubset.Left.quotientMap ideal.toRootSubset hthree).toLinearMap
    (scalar • ideal.singleSpline vertex) ≠ 0
  rw [map_smul]
  exact smul_ne_zero hscalar (HessenbergIdeal.Left.single_class_ne_zero ideal vertex)

end Left
namespace Right

/-- The upward/downward diagonal product has nonzero right quotient class. -/
theorem paired_product_ne_zero (vertex : DihedralGroup n) :
    RootSubset.Right.quotientMap ideal.toRootSubset hthree
      (spline ideal vertex * opposite ideal vertex) ≠ 0 := by
  obtain ⟨scalar, hscalar, heq⟩ := opposite_product_singleton ideal vertex
  rw [heq]
  change (RootSubset.Right.quotientMap ideal.toRootSubset hthree).toLinearMap
    (scalar • ideal.singleSpline vertex) ≠ 0
  rw [map_smul]
  exact smul_ne_zero hscalar (HessenbergIdeal.Right.single_class_ne_zero ideal vertex)

end Right
end Schubert.DihedralSplines.FlowupSpline
