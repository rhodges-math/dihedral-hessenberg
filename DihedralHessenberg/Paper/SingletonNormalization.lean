import DihedralHessenberg.Paper.SingletonBoundary
import DihedralHessenberg.Paper.OppositeFlowup
import DihedralHessenberg.Paper.SingletonTranslation

/-! # Scalar normalization of homogeneous single-vertex spline products -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

/-- Two nonzero singleton-supported splines at the boundary degree are scalar multiples. -/
theorem singleton_scalar (vertex : DihedralGroup n) (first second : selected.Spline)
    (hfirstDegree : first ∈ selected.piece selected.carrier.ncard)
    (hsecondDegree : second ∈ selected.piece selected.carrier.ncard)
    (hfirstSupport : ∀ current, current ≠ vertex →
      (first : DihedralGroup n → CoordinatePolynomial) current = 0)
    (hsecondSupport : ∀ current, current ≠ vertex →
      (second : DihedralGroup n → CoordinatePolynomial) current = 0)
    (hfirst : (first : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hsecond : (second : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧ first = scalar • second := by
  obtain ⟨firstScalar, hfirstScalar⟩ := selected.localized {vertex} first _ hfirstDegree
    (fun current h => hfirstSupport current (by simpa only [Set.mem_singleton_iff] using h))
    vertex (card_singleton_boundary n selected vertex)
  obtain ⟨secondScalar, hsecondScalar⟩ := selected.localized {vertex} second _ hsecondDegree
    (fun current h => hsecondSupport current (by simpa only [Set.mem_singleton_iff] using h))
    vertex (card_singleton_boundary n selected vertex)
  have hfirstNonzero : firstScalar ≠ 0 := by
    intro h
    exact hfirst (by simp [hfirstScalar, h])
  have hsecondNonzero : secondScalar ≠ 0 := by
    intro h
    exact hsecond (by simp [hsecondScalar, h])
  refine ⟨firstScalar / secondScalar, div_ne_zero hfirstNonzero hsecondNonzero, ?_⟩
  apply Subtype.ext
  funext current
  change (first : DihedralGroup n → CoordinatePolynomial) current =
    (firstScalar / secondScalar) •
      (second : DihedralGroup n → CoordinatePolynomial) current
  rw [MvPolynomial.smul_eq_C_mul]
  by_cases heq : current = vertex
  · subst current
    rw [hfirstScalar, hsecondScalar, ← mul_assoc, ← map_mul,
      div_mul_cancel₀ _ hsecondNonzero]
  · rw [hfirstSupport current heq, hsecondSupport current heq, mul_zero]

end Schubert.Dihedral.RootSubset
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Matched flow-up products are nonzero scalar multiples of singletons. -/
theorem opposite_product_singleton (vertex : DihedralGroup n) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧ spline ideal vertex * opposite ideal vertex =
      scalar • ideal.singleSpline vertex := by
  apply ideal.toRootSubset.singleton_scalar vertex _ _
    (opposite_product_homogeneous ideal vertex) (ideal.singleSpline_mem_piece vertex)
    (opposite_product_support ideal vertex) _
    (opposite_product_diagonal ideal vertex) (ideal.singleSpline_nonzero vertex)
  intro current hne
  rw [ideal.singleSpline_apply, ite_eq_right hne]

end Schubert.DihedralSplines.FlowupSpline
