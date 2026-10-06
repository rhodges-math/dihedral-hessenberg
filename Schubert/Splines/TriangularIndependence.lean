import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Order.WellFounded
import Schubert.Splines.Graph

/-! # Independence of triangular spline families

A family of splines supported above its indices is linearly independent when its
diagonal values are nonzero. Well-founded induction proves that every coefficient
of a vanishing finite linear combination is zero.
-/

namespace Schubert.Splines.IdealLabeledGraph

universe u v w

variable {R : Type u} {V : Type v} {E : Type w}
variable [CommRing R] [IsDomain R] [PartialOrder V] [WellFoundedLT V]
variable (graph : IdealLabeledGraph R V E)

/-- A triangular family of splines with nonzero diagonal is linearly independent. -/
theorem linearIndependent_of_triangular (family : V → graph.Spline)
    (hsupport : ∀ first second, ¬ first ≤ second → (family first : V → R) second = 0)
    (hdiagonal : ∀ vertex, (family vertex : V → R) vertex ≠ 0) :
    LinearIndependent R family := by
  classical
  apply linearIndependent_iff'.mpr
  intro indices coefficient hsum vertex hvertex
  have hcoefficients : ∀ vertex, vertex ∈ indices → coefficient vertex = 0 := by
    intro vertex
    refine (wellFounded_lt : WellFounded ((· < ·) : V → V → Prop)).induction
      (C := fun index => index ∈ indices → coefficient index = 0) vertex ?_
    intro vertex ih hvertex
    have hevaluation := congrArg (graph.evaluation vertex) hsum
    have hterms : ∀ other ∈ indices, other ≠ vertex →
        coefficient other * (family other : V → R) vertex = 0 := by
      intro other hother hne
      by_cases hle : other ≤ vertex
      · rw [ih other (lt_of_le_of_ne hle hne) hother, zero_mul]
      · rw [hsupport other vertex hle, mul_zero]
    have hsumEvaluation : (∑ other ∈ indices,
        coefficient other * (family other : V → R) vertex) = 0 := by
      simpa only [map_sum, map_smul, map_zero, evaluation_apply, smul_eq_mul] using hevaluation
    rw [Finset.sum_eq_single vertex (fun other hother hne => hterms other hother hne)
      (fun hnot => (hnot hvertex).elim)] at hsumEvaluation
    exact (mul_eq_zero.mp hsumEvaluation).resolve_right (hdiagonal vertex)
  exact hcoefficients vertex hvertex

end Schubert.Splines.IdealLabeledGraph
