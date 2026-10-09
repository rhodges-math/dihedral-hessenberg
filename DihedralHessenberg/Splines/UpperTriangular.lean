import DihedralHessenberg.Splines.PolynomialGraph
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Upper-triangular splines on ordered vertex sets -/

namespace Schubert.Splines.IdealLabeledGraph
variable {R V E : Type*} [CommRing R] [PartialOrder V]
variable (graph : IdealLabeledGraph R V E)

/-- A spline is nonzero at its indexing vertex and vanishes away from its upper set. -/
def IsUpperAt (value : graph.Spline) (vertex : V) : Prop :=
  (value : V → R) vertex ≠ 0 ∧ ∀ current, ¬ vertex ≤ current → (value : V → R) current = 0

/-- Each indexed spline in the family is upper triangular at its own vertex. -/
def IsUpperFamily (family : V → graph.Spline) : Prop :=
  ∀ vertex, graph.IsUpperAt (family vertex) vertex

/-- Upper triangularity is exactly diagonal nonvanishing and upper-set support. -/
theorem upperAt_iff (value : graph.Spline) (vertex : V) :
    graph.IsUpperAt value vertex ↔ (value : V → R) vertex ≠ 0 ∧
      ∀ current, ¬ vertex ≤ current → (value : V → R) current = 0 := Iff.rfl

/-- Support contains the indexing vertex and lies in its upper set. -/
theorem upperAt_support_iff (value : graph.Spline) (vertex : V) :
    graph.IsUpperAt value vertex ↔ vertex ∈ Function.support (value : V → R) ∧
      Function.support (value : V → R) ⊆ Set.Ici vertex := by
  constructor
  · rintro ⟨hvertex, hsupport⟩
    refine ⟨hvertex, ?_⟩
    intro current hcurrent
    by_contra hnot
    exact hcurrent (hsupport current hnot)
  · rintro ⟨hvertex, hsupport⟩
    refine ⟨hvertex, ?_⟩
    intro current hnot
    by_contra hcurrent
    exact hnot (hsupport hcurrent)

/-- A linear extension orders the family evaluation matrix upper triangularly. -/
theorem upper_matrix {I : Type*} [LinearOrder I] (order : I ≃ V)
    (hextension : ∀ first second : V, first ≤ second → order.symm first ≤ order.symm second)
    (family : V → graph.Spline) (hfamily : graph.IsUpperFamily family) :
    Matrix.IsUpperTriangular
      (fun first second : I => (family (order first) : V → R) (order second)) := by
  intro first second hbelow
  apply (hfamily (order first)).2 (order second)
  intro hle
  have hpositions := hextension (order first) (order second) hle
  have hindex : first ≤ second := by simpa only [Equiv.symm_apply_apply] using hpositions
  exact (not_le_of_gt hbelow) hindex
end Schubert.Splines.IdealLabeledGraph

namespace Schubert.Splines.PolynomialGraph
variable {R V E : Type*} [CommRing R] [PartialOrder V]
variable (graph : PolynomialGraph R V E)

/-- Polynomial-labelled spline upper triangularity retains the vertex values. -/
def IsUpperAt (value : graph.Spline) (vertex : V) : Prop :=
  (value : V → R) vertex ≠ 0 ∧ ∀ current, ¬ vertex ≤ current → (value : V → R) current = 0

/-- A polynomial-labelled family is upper triangular at every indexing vertex. -/
def IsUpperFamily (family : V → graph.Spline) : Prop :=
  ∀ vertex, graph.IsUpperAt (family vertex) vertex

/-- Replacing each label by its principal ideal preserves exact upper triangularity. -/
theorem upperAt_ideal (value : graph.Spline) (vertex : V) :
    graph.IsUpperAt value vertex ↔
      graph.idealGraph.IsUpperAt (graph.idealEquiv value) vertex := Iff.rfl

/-- Exact polynomial family upper triangularity is preserved under the value-identical map. -/
theorem upperFamily_ideal (family : V → graph.Spline) :
    graph.IsUpperFamily family ↔ graph.idealGraph.IsUpperFamily
      (fun vertex => graph.idealEquiv (family vertex)) := Iff.rfl

/-- Linear extensions make the polynomial family evaluation matrix upper triangular. -/
theorem upper_matrix {I : Type*} [LinearOrder I] (order : I ≃ V)
    (hextension : ∀ first second : V, first ≤ second → order.symm first ≤ order.symm second)
    (family : V → graph.Spline) (hfamily : graph.IsUpperFamily family) :
    Matrix.IsUpperTriangular
      (fun first second : I => (family (order first) : V → R) (order second)) :=
  graph.idealGraph.upper_matrix order hextension
    (fun vertex => graph.idealEquiv (family vertex)) hfamily
end Schubert.Splines.PolynomialGraph
