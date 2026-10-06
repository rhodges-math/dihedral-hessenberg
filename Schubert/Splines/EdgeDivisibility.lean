import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Span
import Schubert.Splines.Graph

/-! # Products of incident labels divide spline values

When a spline vanishes at the other endpoints of a collection of edges, their labels
divide its value at their common endpoint. Pairwise relatively prime labels can then be
combined into one product divisibility statement.
-/

namespace Schubert.Splines.IdealLabeledGraph

universe u v w

variable {R : Type u} {V : Type v} {E : Type w} [CommRing R]
variable (graph : IdealLabeledGraph R V E)

/-- A principal edge label divides a spline value when the other endpoint vanishes. -/
theorem label_dvd_of_target_eq_zero (value : graph.Spline) (edge : E) (label : R)
    (hlabel : graph.label edge = Ideal.span {label})
    (hzero : (value : V → R) (graph.target edge) = 0) :
    label ∣ (value : V → R) (graph.source edge) := by
  have hcondition := graph.spline_condition value edge
  rw [hlabel, hzero, sub_zero] at hcondition
  exact Ideal.mem_span_singleton.mp hcondition

/-- Pairwise relatively prime labels at a common endpoint divide its value jointly. -/
theorem prod_labels_dvd_of_targets_eq_zero [DecompositionMonoid R]
    (value : graph.Spline) (vertex : V) (edges : Finset E) (labels : E → R)
    (hsource : ∀ edge ∈ edges, graph.source edge = vertex)
    (hlabels : ∀ edge ∈ edges, graph.label edge = Ideal.span {labels edge})
    (hrelPrime : (edges : Set E).Pairwise (fun first second =>
      IsRelPrime (labels first) (labels second)))
    (hzero : ∀ edge ∈ edges, (value : V → R) (graph.target edge) = 0) :
    (∏ edge ∈ edges, labels edge) ∣ (value : V → R) vertex := by
  apply Finset.prod_dvd_of_isRelPrime hrelPrime
  intro edge hedge
  simpa only [hsource edge hedge] using
    graph.label_dvd_of_target_eq_zero value edge (labels edge)
      (hlabels edge hedge) (hzero edge hedge)

end Schubert.Splines.IdealLabeledGraph
