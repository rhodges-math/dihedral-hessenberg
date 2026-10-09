import DihedralHessenberg.Paper.FlowupCosetSpan
import DihedralHessenberg.Paper.FlowupOrbitIndependence

/-! # Independence of the high flow-up orbit indexed by its values -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The high flow-up orbit is independent under the short selection hypotheses. -/
theorem orbit_independent_short (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hbound : 2 * (n - length n hthree vertex - 1) + 1 < n)
    (hselected : ∀ beta : PositiveRoot n,
      length n hthree beta.reflection ≤ 2 * (n - length n hthree vertex - 1) + 1 →
        beta.val ∈ ideal) :
    letI := ideal.toRootSubset.dotMulAction hthree
    LinearIndependent ℂ (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
      (value : ideal.toRootSubset.Spline)) := by
  classical
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal vertex)).fintype
  let translate (value : MulAction.orbit (DihedralGroup n) (spline ideal vertex)) :=
    Classical.choose (MulAction.mem_orbit_iff.mp value.property)
  have htranslate : ∀ value, ideal.toRootSubset.dot hthree (translate value)
      (spline ideal vertex) = value.val := fun value =>
    Classical.choose_spec (MulAction.mem_orbit_iff.mp value.property)
  have hinjective : Function.Injective (fun value =>
      ideal.toRootSubset.dot hthree (translate value) (spline ideal vertex)) := by
    intro first second hequal
    apply Subtype.ext
    rw [← htranslate first, ← htranslate second]
    exact hequal
  have hindependent := high_orbit_independent ideal vertex alpha hsimple hascent hhalf hedge
    hbound hselected translate hinjective
  have hfamily : (fun value => ideal.toRootSubset.dot hthree (translate value)
      (spline ideal vertex)) = fun value => value.val := funext htranslate
  rw [hfamily] at hindependent
  exact hindependent

/-- The high flow-up orbit is independent under the odd selection hypotheses. -/
theorem orbit_independent_odd (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hcard : ideal.carrier.ncard = 2 * (n - length n hthree vertex - 1) + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    letI := ideal.toRootSubset.dotMulAction hthree
    LinearIndependent ℂ (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
      (value : ideal.toRootSubset.Spline)) := by
  classical
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal vertex)).fintype
  let translate (value : MulAction.orbit (DihedralGroup n) (spline ideal vertex)) :=
    Classical.choose (MulAction.mem_orbit_iff.mp value.property)
  have htranslate : ∀ value, ideal.toRootSubset.dot hthree (translate value)
      (spline ideal vertex) = value.val := fun value =>
    Classical.choose_spec (MulAction.mem_orbit_iff.mp value.property)
  have hinjective : Function.Injective (fun value =>
      ideal.toRootSubset.dot hthree (translate value) (spline ideal vertex)) := by
    intro first second hequal
    apply Subtype.ext
    rw [← htranslate first, ← htranslate second]
    exact hequal
  have hindependent := high_odd_orbit_independent ideal vertex alpha hsimple hascent hhalf hedge
    hcard hproper translate hinjective
  have hfamily : (fun value => ideal.toRootSubset.dot hthree (translate value)
      (spline ideal vertex)) = fun value => value.val := funext htranslate
  rw [hfamily] at hindependent
  exact hindependent

end Schubert.DihedralSplines.FlowupSpline
