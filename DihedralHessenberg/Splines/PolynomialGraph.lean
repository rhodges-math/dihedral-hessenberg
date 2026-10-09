import DihedralHessenberg.Splines.Graph
import Mathlib.RingTheory.Ideal.Span

/-! # Graphs with polynomial labels

A polynomial label specifies a generator, including its sign. Its principal ideal
imposes the spline condition on the endpoint values.
-/

namespace Schubert.Splines

universe u v w

/-- A graph whose edge labels are specified ring elements. -/
structure PolynomialGraph (R : Type u) (V : Type v) (E : Type w) [CommRing R] where
  /-- The first endpoint. -/
  source : E → V
  /-- The second endpoint. -/
  target : E → V
  /-- The specified polynomial generator on each edge. -/
  label : E → R

namespace PolynomialGraph

variable {R : Type u} {V : Type v} {E : Type w} [CommRing R]
variable (graph : PolynomialGraph R V E)

/-- Replace every polynomial label by the principal ideal it generates. -/
def idealGraph : IdealLabeledGraph R V E where
  source := graph.source
  target := graph.target
  label edge := Ideal.span {graph.label edge}

/-- Every edge label divides the difference of its endpoint values. -/
def IsSpline (value : V → R) : Prop :=
  ∀ edge, graph.label edge ∣ value (graph.source edge) - value (graph.target edge)

/-- Polynomial and principal-ideal labels impose the same spline condition. -/
theorem isSpline_iff (value : V → R) :
    graph.IsSpline value ↔ graph.idealGraph.IsSpline value := by
  simp only [IsSpline, IdealLabeledGraph.IsSpline, idealGraph, Ideal.mem_span_singleton]

/-- The polynomial spline condition defines a function subalgebra. -/
def splineAlgebra : Subalgebra R (V → R) where
  carrier := {value | graph.IsSpline value}
  algebraMap_mem' scalar :=
    (graph.isSpline_iff _).2 (graph.idealGraph.isSpline_const scalar)
  add_mem' first second :=
    (graph.isSpline_iff _).2 (graph.idealGraph.isSpline_add
      ((graph.isSpline_iff _).1 first) ((graph.isSpline_iff _).1 second))
  mul_mem' first second :=
    (graph.isSpline_iff _).2 (graph.idealGraph.isSpline_mul
      ((graph.isSpline_iff _).1 first) ((graph.isSpline_iff _).1 second))

/-- The polynomial and ideal spline subalgebras coincide. -/
theorem splineAlgebra_eq : graph.splineAlgebra = graph.idealGraph.splineAlgebra := by
  ext value
  exact graph.isSpline_iff value

/-- Polynomial-labelled splines as vertex functions. -/
abbrev Spline := ↥graph.splineAlgebra

/-- The condition on a packaged polynomial-labelled spline. -/
theorem condition (value : graph.Spline) (edge : E) :
    graph.label edge ∣ (value : V → R) (graph.source edge) -
      (value : V → R) (graph.target edge) :=
  value.property edge

/-- Replacing labels by generated ideals preserves values and algebra operations. -/
def idealEquiv : graph.Spline ≃ₐ[R] graph.idealGraph.Spline where
  toFun value := ⟨value.val, (graph.isSpline_iff value.val).1 value.property⟩
  invFun value := ⟨value.val, (graph.isSpline_iff value.val).2 value.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- The principal-ideal equivalence preserves every evaluation. -/
theorem idealEquiv_apply (value : graph.Spline) (vertex : V) :
    (graph.idealEquiv value : V → R) vertex = (value : V → R) vertex :=
  rfl

end PolynomialGraph

end Schubert.Splines
