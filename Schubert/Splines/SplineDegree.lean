import Schubert.Splines.FinitePolynomialGrading

/-! # Whole-spline degree bounds

The degree of a finite-vertex spline is the maximum total degree of its values.
-/

namespace Schubert.Splines.IdealLabeledGraph

universe u v w z

variable {K : Type u} {T : Type v} {V : Type w} {E : Type z}
variable [CommRing K] [Fintype V]
variable (graph : IdealLabeledGraph (MvPolynomial T K) V E)

/-- A whole-spline degree bound is exactly the bound at every vertex. -/
theorem degreeBound_le_iff (value : graph.Spline) (degree : ℕ) :
    graph.degreeBound value ≤ degree ↔
      ∀ vertex, ((value : V → MvPolynomial T K) vertex).totalDegree ≤ degree := by
  classical
  simp only [degreeBound, Finset.sup_le_iff, Finset.mem_univ, forall_const]

/-- On a nonempty finite vertex set, the whole-spline degree occurs at a vertex. -/
theorem degreeBound_attained [Nonempty V] (value : graph.Spline) :
    ∃ vertex, graph.degreeBound value =
      ((value : V → MvPolynomial T K) vertex).totalDegree := by
  classical
  obtain ⟨vertex, _, hdegree⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun vertex => ((value : V → MvPolynomial T K) vertex).totalDegree)
  exact ⟨vertex, hdegree⟩

end Schubert.Splines.IdealLabeledGraph
