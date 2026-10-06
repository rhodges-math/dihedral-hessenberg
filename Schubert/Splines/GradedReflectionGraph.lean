import Schubert.Splines.DotAction
import Schubert.Splines.PolynomialGrading

/-! # Grading data for reflection splines

Polynomial reflection data has degree-one labels and coefficient automorphisms preserving
each homogeneous polynomial degree. Its edge ideals are homogeneous, and its spline
degree pieces and homogeneous projections use the standard polynomial components.
The dot action preserves each degree piece. No finite group or quotient is assumed here.
-/

namespace Schubert.Splines

universe u v w z

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial reflection data with linear labels and degree-preserving coefficient action. -/
structure GradedReflectionGraphData (K : Type u) (P : Type v) (W : Type w) (T : Type z)
    [CommRing K] [Group W] extends ReflectionGraphData K (MvPolynomial P K) W T where
  /-- Every reflection label is homogeneous of polynomial degree one. -/
  label_homogeneous : ∀ index, (label index).IsHomogeneous 1
  /-- The coefficient action preserves every homogeneous polynomial degree. -/
  action_homogeneous : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
    (action element polynomial).IsHomogeneous degree

namespace GradedReflectionGraphData

variable {K : Type u} {P : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [Group W]
variable (data : GradedReflectionGraphData K P W T)

/-- Reflection-edge ideals are homogeneous because their generating labels have degree one. -/
theorem edgeIdeal_homogeneous (selected : Set T) (edge : W × selected) :
    ((data.toReflectionGraphData.reflectionGraph selected).label edge).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule P K) := by
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule P K)
  intro polynomial hpolynomial
  rcases Set.mem_singleton_iff.mp hpolynomial with rfl
  exact ⟨1, data.action_homogeneous edge.1 1 (data.label edge.2)
    (data.label_homogeneous edge.2)⟩

/-- The homogeneous degree piece of the selected reflection spline algebra. -/
noncomputable def homogeneousPiece (selected : Set T) (degree : ℕ) :
    Submodule K (data.toReflectionGraphData.Spline selected) :=
  (data.toReflectionGraphData.reflectionGraph selected).homogeneousPiece degree

/-- Homogeneous polynomial projection on the selected reflection splines. -/
noncomputable def homogeneousComponent (selected : Set T) (degree : ℕ) :
    data.toReflectionGraphData.Spline selected →ₗ[K] data.toReflectionGraphData.Spline selected :=
  (data.toReflectionGraphData.reflectionGraph selected).homogeneousComponent
    (data.edgeIdeal_homogeneous selected) degree

/-- The projection onto a reflection spline degree piece belongs to that piece. -/
theorem homogeneousComponent_mem (selected : Set T) (degree : ℕ)
    (value : data.toReflectionGraphData.Spline selected) :
    data.homogeneousComponent selected degree value ∈ data.homogeneousPiece selected degree :=
  (data.toReflectionGraphData.reflectionGraph selected).homogeneousComponent_mem
    (data.edgeIdeal_homogeneous selected) degree value

/-- The dot action preserves each homogeneous reflection spline degree piece. -/
theorem dot_mem_homogeneousPiece (selected : Set T) (element : W) (degree : ℕ)
    (value : data.toReflectionGraphData.Spline selected)
    (hvalue : value ∈ data.homogeneousPiece selected degree) :
    data.toReflectionGraphData.dot selected element value ∈
      data.homogeneousPiece selected degree := by
  intro vertex
  exact data.action_homogeneous element degree
    ((value : W → MvPolynomial P K) (element⁻¹ * vertex)) (hvalue (element⁻¹ * vertex))

end GradedReflectionGraphData

end Schubert.Splines
