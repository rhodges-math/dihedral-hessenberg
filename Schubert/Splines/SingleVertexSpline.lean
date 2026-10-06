import Schubert.Splines.ReflectionGraph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.Divisibility.Basic

/-! # Reflection splines supported at one vertex -/

namespace Schubert.Splines.ReflectionGraphData

variable {K S W T : Type*} [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable (data : ReflectionGraphData K S W T) (selected : Set T)

/-- A value divisible by all incident labels gives a spline supported at one vertex. -/
theorem singleFunction_isSpline [DecidableEq W] (vertex : W) (polynomial : S)
    (hdivides : ∀ index ∈ selected, data.action vertex (data.label index) ∣ polynomial) :
    (data.reflectionGraph selected).IsSpline
      (fun current => if current = vertex then polynomial else 0) := by
  classical
  intro edge
  apply Ideal.mem_span_singleton.mpr
  change data.action edge.1 (data.label edge.2) ∣
    (if edge.1 = vertex then polynomial else 0) -
      (if edge.1 * data.reflection edge.2 = vertex then polynomial else 0)
  by_cases hsource : edge.1 = vertex
  · rw [hsource]
    by_cases htarget : vertex * data.reflection edge.2 = vertex
    · simp only [ite_true, htarget, sub_self, dvd_zero]
    · simpa only [ite_true, htarget, ite_false, sub_zero] using
        hdivides edge.2 edge.2.property
  · by_cases htarget : edge.1 * data.reflection edge.2 = vertex
    · have hreverse : edge.1 = vertex * data.reflection edge.2 := by
        rw [← htarget, data.reflection_edge_reverse]
      rw [ite_eq_right hsource, ite_eq_left htarget, zero_sub, hreverse,
        data.reflection_label_reverse]
      exact (hdivides edge.2 edge.2.property).neg_left.neg_right
    · simp only [hsource, htarget, ite_false, sub_self, dvd_zero]

/-- The product of selected incident labels gives a spline supported at any chosen vertex. -/
theorem singleProductFunction_isSpline [DecidableEq W]
    (indices : Finset T) (vertex : W) :
    (data.reflectionGraph (indices : Set T)).IsSpline
      (fun current => if current = vertex then
        ∏ index ∈ indices, data.action vertex (data.label index) else 0) := by
  apply data.singleFunction_isSpline (indices : Set T)
  intro index hindex
  exact Finset.dvd_prod_of_mem (fun index => data.action vertex (data.label index)) hindex

end Schubert.Splines.ReflectionGraphData
