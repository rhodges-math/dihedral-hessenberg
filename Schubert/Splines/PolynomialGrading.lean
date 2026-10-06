import Schubert.Splines.Graph
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Homogeneous pieces and projections of polynomial splines

The degree pieces consist of splines whose values all have the same homogeneous degree.
Homogeneous edge ideals permit projection onto each piece. These constructions need no
finite vertex set; assembling them into a direct-sum grading is a separate finite-support
obligation.
-/

namespace Schubert.Splines.IdealLabeledGraph

universe u v w z

variable {K : Type u} {T : Type v} {V : Type w} {E : Type z} [CommRing K]
variable (graph : IdealLabeledGraph (MvPolynomial T K) V E)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Splines whose value at every vertex is homogeneous of the given degree. -/
def homogeneousPiece (degree : ℕ) : Submodule K graph.Spline where
  carrier := {value | ∀ vertex, ((value : V → MvPolynomial T K) vertex).IsHomogeneous degree}
  zero_mem' := by
    intro vertex
    exact (MvPolynomial.homogeneousSubmodule T K degree).zero_mem
  add_mem' hfirst hsecond := by
    intro vertex
    exact (hfirst vertex).add (hsecond vertex)
  smul_mem' scalar value hvalue := by
    intro vertex
    exact (MvPolynomial.homogeneousSubmodule T K degree).smul_mem scalar (hvalue vertex)

/-- Membership in a spline degree piece is pointwise polynomial homogeneity. -/
theorem mem_homogeneousPiece (degree : ℕ) (value : graph.Spline) :
    value ∈ graph.homogeneousPiece degree ↔
      ∀ vertex, ((value : V → MvPolynomial T K) vertex).IsHomogeneous degree :=
  Iff.rfl

/-- Multiplication adds the homogeneous degrees of spline values. -/
theorem mul_mem_homogeneousPiece {firstDegree secondDegree : ℕ}
    {first second : graph.Spline} (hfirst : first ∈ graph.homogeneousPiece firstDegree)
    (hsecond : second ∈ graph.homogeneousPiece secondDegree) :
    first * second ∈ graph.homogeneousPiece (firstDegree + secondDegree) := by
  intro vertex
  exact (hfirst vertex).mul (hsecond vertex)

/-- Polynomial homogeneous projections preserve splines with homogeneous edge ideals. -/
theorem homogeneousComponent_isSpline
    (hlabels : ∀ edge, (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))
    (degree : ℕ) (value : graph.Spline) :
    graph.IsSpline (fun vertex =>
      MvPolynomial.homogeneousComponent degree ((value : V → MvPolynomial T K) vertex)) := by
  intro edge
  have hprojection := MvPolynomial.homogeneousComponent_mem_of_mem (hlabels edge)
    (graph.spline_condition value edge) degree
  simpa only [map_sub] using hprojection

/-- The homogeneous-component linear map on polynomial splines. -/
noncomputable def homogeneousComponent
    (hlabels : ∀ edge, (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))
    (degree : ℕ) : graph.Spline →ₗ[K] graph.Spline where
  toFun value := ⟨fun vertex =>
    MvPolynomial.homogeneousComponent degree ((value : V → MvPolynomial T K) vertex),
    graph.homogeneousComponent_isSpline hlabels degree value⟩
  map_add' first second := by
    apply Subtype.ext
    funext vertex
    exact map_add (MvPolynomial.homogeneousComponent degree) _ _
  map_smul' scalar value := by
    apply Subtype.ext
    funext vertex
    exact map_smul (MvPolynomial.homogeneousComponent degree) scalar _

/-- Spline homogeneous projection is evaluated by projecting its polynomial value. -/
theorem homogeneousComponent_apply
    (hlabels : ∀ edge, (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))
    (degree : ℕ) (value : graph.Spline) (vertex : V) :
    (graph.homogeneousComponent hlabels degree value : V → MvPolynomial T K) vertex =
      MvPolynomial.homogeneousComponent degree ((value : V → MvPolynomial T K) vertex) :=
  rfl

/-- The homogeneous projection takes values in its designated spline degree piece. -/
theorem homogeneousComponent_mem
    (hlabels : ∀ edge, (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))
    (degree : ℕ) (value : graph.Spline) :
    graph.homogeneousComponent hlabels degree value ∈ graph.homogeneousPiece degree := by
  intro vertex
  exact MvPolynomial.homogeneousComponent_isHomogeneous _ _

/-- Projection fixes a spline already in the specified degree piece. -/
theorem homogeneousComponent_eq_self
    (hlabels : ∀ edge, (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))
    (degree : ℕ) (value : graph.Spline) (hvalue : value ∈ graph.homogeneousPiece degree) :
    graph.homogeneousComponent hlabels degree value = value := by
  apply Subtype.ext
  funext vertex
  exact MvPolynomial.homogeneousComponent_eq_self (hvalue vertex)

end Schubert.Splines.IdealLabeledGraph
