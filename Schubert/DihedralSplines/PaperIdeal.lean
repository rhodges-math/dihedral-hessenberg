import Schubert.DihedralSplines.PaperSpline
import Schubert.DihedralSplines.HessenbergObjectBridge

/-! # Evaluation-preserving spline transport for vector Hessenberg ideals -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)

/-- The vector Hessenberg condition equals its finite indexed condition. -/
theorem isSpline_iff (value : DihedralGroup n → CoordinatePolynomial) :
    ideal.toRootSubset.IsSpline value ↔ (hessenbergGraph ideal.indexed).IsSpline value := by
  change _ ↔ ((dihedralReflectionData n hthree).reflectionGraph
    (ideal.indexed.roots : Set (PositiveRootIndex n))).IsSpline value
  rw [ideal.indexed_roots]
  exact ideal.toRootSubset.isSpline_iff_backend hthree value

/-- Reindexing the roots preserves the entire geometric spline algebra. -/
def splineEquiv : ideal.toRootSubset.Spline ≃ₐ[ℂ] HessenbergSpline ideal.indexed where
  toFun value := ⟨value.val, (ideal.isSpline_iff value.val).1 value.property⟩
  invFun value := ⟨value.val, (ideal.isSpline_iff value.val).2 value.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The Hessenberg algebra equivalence preserves each evaluation. -/
theorem splineEquiv_apply (value : ideal.toRootSubset.Spline) (vertex : DihedralGroup n) :
    (ideal.splineEquiv value : DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex := rfl

/-- Root reindexing preserves the maximum polynomial degree of a spline. -/
theorem splineEquiv_degree [NeZero n] (value : ideal.toRootSubset.Spline) :
    (hessenbergGraph ideal.indexed).degreeBound (ideal.splineEquiv value) =
      ideal.toRootSubset.degree value := rfl

end Schubert.DihedralSplines.HessenbergIdeal
