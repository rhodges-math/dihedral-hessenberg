import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Tactic.Ring

/-! # Splines on graphs with ideal labels

An ideal-labeled graph consists of vertices, edges, endpoint maps, and an ideal at each edge.
A spline assigns ring elements to vertices so that each endpoint difference lies in its edge
ideal. Splines form a subalgebra of the ring of vertex functions, with pointwise operations.
No finiteness, symmetry, or distinctness of edges is required.
-/

namespace Schubert.Splines

universe u v w

/-- A graph with specified endpoints and an ideal label at each edge. -/
structure IdealLabeledGraph (R : Type u) (V : Type v) (E : Type w) [CommRing R] where
  /-- The first endpoint of each edge. -/
  source : E → V
  /-- The second endpoint of each edge. -/
  target : E → V
  /-- The ideal imposing the endpoint congruence at each edge. -/
  label : E → Ideal R

namespace IdealLabeledGraph

variable {R : Type u} {V : Type v} {E : Type w} [CommRing R]
variable (graph : IdealLabeledGraph R V E)

/-- A vertex function is a spline if its endpoint difference belongs to every edge ideal. -/
def IsSpline (value : V → R) : Prop :=
  ∀ edge, value (graph.source edge) - value (graph.target edge) ∈ graph.label edge

/-- Constant vertex functions are splines. -/
theorem isSpline_const (scalar : R) : graph.IsSpline (fun _ => scalar) := by
  intro edge
  simpa only [sub_self] using (graph.label edge).zero_mem

/-- The sum of two splines is a spline. -/
theorem isSpline_add {first second : V → R}
    (hfirst : graph.IsSpline first) (hsecond : graph.IsSpline second) :
    graph.IsSpline (first + second) := by
  intro edge
  change (first (graph.source edge) + second (graph.source edge)) -
    (first (graph.target edge) + second (graph.target edge)) ∈ graph.label edge
  rw [show (first (graph.source edge) + second (graph.source edge)) -
      (first (graph.target edge) + second (graph.target edge)) =
      (first (graph.source edge) - first (graph.target edge)) +
        (second (graph.source edge) - second (graph.target edge)) by ring]
  exact (graph.label edge).add_mem (hfirst edge) (hsecond edge)

/-- The pointwise product of two splines is a spline. -/
theorem isSpline_mul {first second : V → R}
    (hfirst : graph.IsSpline first) (hsecond : graph.IsSpline second) :
    graph.IsSpline (first * second) := by
  intro edge
  change first (graph.source edge) * second (graph.source edge) -
    first (graph.target edge) * second (graph.target edge) ∈ graph.label edge
  rw [show first (graph.source edge) * second (graph.source edge) -
      first (graph.target edge) * second (graph.target edge) =
      first (graph.source edge) *
          (second (graph.source edge) - second (graph.target edge)) +
        second (graph.target edge) *
          (first (graph.source edge) - first (graph.target edge)) by ring]
  exact (graph.label edge).add_mem
    ((graph.label edge).mul_mem_left _ (hsecond edge))
    ((graph.label edge).mul_mem_left _ (hfirst edge))

/-- Splines as a subalgebra of the algebra of all vertex functions. -/
def splineAlgebra : Subalgebra R (V → R) where
  carrier := {value | graph.IsSpline value}
  algebraMap_mem' scalar := by
    change graph.IsSpline (fun _ => scalar)
    exact graph.isSpline_const scalar
  add_mem' := graph.isSpline_add
  mul_mem' := graph.isSpline_mul

theorem mem_splineAlgebra {value : V → R} :
    value ∈ graph.splineAlgebra ↔ graph.IsSpline value :=
  Iff.rfl

/-- The type of splines on an ideal-labeled graph. -/
abbrev Spline := ↥graph.splineAlgebra

/-- A spline satisfies the ideal congruence along each edge. -/
theorem spline_condition (value : graph.Spline) (edge : E) :
    (value : V → R) (graph.source edge) - (value : V → R) (graph.target edge) ∈
      graph.label edge :=
  value.property edge

/-- Splines are equal when their values agree at every vertex. -/
@[ext]
theorem spline_ext {first second : graph.Spline}
    (hequal : ∀ vertex, (first : V → R) vertex = (second : V → R) vertex) :
    first = second :=
  Subtype.ext (funext hequal)

/-- The spline with the given constant value at every vertex. -/
def constant (scalar : R) : graph.Spline :=
  ⟨fun _ => scalar, graph.isSpline_const scalar⟩

theorem constant_apply (scalar : R) (vertex : V) :
    (graph.constant scalar : V → R) vertex = scalar :=
  rfl

/-- Evaluation at a vertex as a homomorphism of algebras. -/
def evaluation (vertex : V) : graph.Spline →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : V => R) vertex).comp graph.splineAlgebra.val

theorem evaluation_apply (vertex : V) (value : graph.Spline) :
    graph.evaluation vertex value = (value : V → R) vertex :=
  rfl

end IdealLabeledGraph

end Schubert.Splines
