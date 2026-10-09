import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.GradedAlgebra.Basic
import Lean.Elab.Tactic.Omega
import DihedralHessenberg.Splines.PolynomialGrading

/-! # Finite-vertex direct-sum grading of polynomial splines

Polynomial values on finitely many vertices have a uniform total-degree bound.
Homogeneous edge ideals therefore let every spline be reconstructed from finitely many
of its homogeneous projections. The homogeneous pieces form an internal direct sum,
which supplies a named graded-algebra structure through the standard direct-sum API.
-/

namespace Schubert.Splines.IdealLabeledGraph

open scoped DirectSum

universe u v w z

variable {K : Type u} {T : Type v} {V : Type w} {E : Type z} [CommRing K]
variable (graph : IdealLabeledGraph (MvPolynomial T K) V E)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (hlabels : ∀ edge,
  (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule T K))

/-- Projecting a homogeneous spline selects its degree and kills all other degrees. -/
theorem homogeneousComponent_of_mem {degree rowDegree : ℕ} (value : graph.Spline)
    (hvalue : value ∈ graph.homogeneousPiece rowDegree) :
    graph.homogeneousComponent hlabels degree value =
      if degree = rowDegree then value else 0 := by
  by_cases heq : degree = rowDegree
  · subst degree
    rw [ite_eq_left rfl]
    exact graph.homogeneousComponent_eq_self hlabels rowDegree value hvalue
  · rw [ite_eq_right heq]
    apply graph.spline_ext
    intro vertex
    change MvPolynomial.homogeneousComponent degree
      ((value : V → MvPolynomial T K) vertex) = 0
    simpa only [ite_eq_right heq] using
      MvPolynomial.homogeneousComponent_of_mem (hvalue vertex) (m := degree)

/-- Projecting the sum of a direct-sum element recovers its designated summand. -/
theorem homogeneousComponent_coeLinearMap (degree : ℕ)
    (pieces : ⨁ index, graph.homogeneousPiece index) :
    graph.homogeneousComponent hlabels degree
        (DirectSum.coeLinearMap graph.homogeneousPiece pieces) =
      (pieces degree : graph.Spline) := by
  classical
  induction pieces using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, Submodule.coe_zero]
  | of index value =>
    rw [DirectSum.coeLinearMap_of, graph.homogeneousComponent_of_mem hlabels value value.property]
    by_cases heq : degree = index
    · subst degree
      rw [ite_eq_left rfl, DirectSum.of_eq_same]
    · rw [ite_eq_right heq, DirectSum.of_eq_of_ne _ _ _ heq]
      rfl
  | add first second hfirst hsecond =>
    rw [map_add, map_add]
    change _ = (first degree : graph.Spline) + (second degree : graph.Spline)
    exact congrArg₂ (· + ·) hfirst hsecond

include hlabels in
/-- The homogeneous pieces have injective direct-sum recomposition, even for infinite vertices. -/
theorem homogeneousPiece_coeLinearMap_injective :
    Function.Injective (DirectSum.coeLinearMap graph.homogeneousPiece) := by
  intro first second heq
  apply DFinsupp.ext
  intro degree
  apply Subtype.ext
  rw [← graph.homogeneousComponent_coeLinearMap hlabels degree first,
    ← graph.homogeneousComponent_coeLinearMap hlabels degree second, heq]

/-- The maximum polynomial degree among the values of a finite-vertex spline. -/
noncomputable def degreeBound [Fintype V] (value : graph.Spline) : ℕ :=
  Finset.univ.sup fun vertex => ((value : V → MvPolynomial T K) vertex).totalDegree

/-- Every vertex value has total degree at most the finite-vertex bound. -/
theorem totalDegree_le_degreeBound [Fintype V] (value : graph.Spline) (vertex : V) :
    ((value : V → MvPolynomial T K) vertex).totalDegree ≤ graph.degreeBound value := by
  classical
  exact Finset.le_sup (f := fun vertex =>
    ((value : V → MvPolynomial T K) vertex).totalDegree) (Finset.mem_univ vertex)

/-- Homogeneous projections vanish above the common finite-vertex degree bound. -/
theorem _root_.Schubert.Splines.IdealLabeledGraph.component_zero_above_degree [Fintype V]
    (degree : ℕ) (value : graph.Spline) (hdegree : graph.degreeBound value < degree) :
    graph.homogeneousComponent hlabels degree value = 0 := by
  apply graph.spline_ext
  intro vertex
  exact MvPolynomial.homogeneousComponent_eq_zero degree _
    ((graph.totalDegree_le_degreeBound value vertex).trans_lt hdegree)

/-- A finite-vertex polynomial spline is the finite sum of its homogeneous projections. -/
theorem sum_homogeneousComponent [Fintype V] (value : graph.Spline) :
    (∑ degree ∈ Finset.range (graph.degreeBound value + 1),
      graph.homogeneousComponent hlabels degree value) = value := by
  classical
  apply graph.spline_ext
  intro vertex
  change graph.evaluation vertex _ = graph.evaluation vertex value
  rw [map_sum]
  simp only [evaluation_apply, homogeneousComponent_apply]
  have hbound := graph.totalDegree_le_degreeBound value vertex
  have hsubset : Finset.range (((value : V → MvPolynomial T K) vertex).totalDegree + 1) ⊆
      Finset.range (graph.degreeBound value + 1) :=
    Finset.range_mono (Nat.add_le_add_right hbound 1)
  rw [← Finset.sum_subset hsubset]
  · exact MvPolynomial.sum_homogeneousComponent _
  · intro degree _ hnot
    apply MvPolynomial.homogeneousComponent_eq_zero degree _
    have hnotlt : ¬ degree < ((value : V → MvPolynomial T K) vertex).totalDegree + 1 := by
      simpa only [Finset.mem_range] using hnot
    omega

include hlabels in
/-- Finite-vertex homogeneous pieces span every polynomial spline. -/
theorem homogeneousPiece_coeLinearMap_surjective [Fintype V] :
    Function.Surjective (DirectSum.coeLinearMap graph.homogeneousPiece) := by
  classical
  intro value
  refine ⟨∑ degree ∈ Finset.range (graph.degreeBound value + 1),
    DirectSum.of (fun index => graph.homogeneousPiece index) degree
      ⟨graph.homogeneousComponent hlabels degree value,
        graph.homogeneousComponent_mem hlabels degree value⟩, ?_⟩
  simpa only [map_sum, DirectSum.coeLinearMap_of] using
    graph.sum_homogeneousComponent hlabels value

include hlabels in
/-- Polynomial spline homogeneous pieces form an internal direct sum for finite vertices. -/
theorem homogeneousPiece_isInternal [Fintype V] :
    DirectSum.IsInternal graph.homogeneousPiece :=
  ⟨graph.homogeneousPiece_coeLinearMap_injective hlabels,
    graph.homogeneousPiece_coeLinearMap_surjective hlabels⟩

/-- The homogeneous spline pieces are closed under the graded ring operations. -/
theorem homogeneousPieceGradedMonoid : SetLike.GradedMonoid graph.homogeneousPiece where
  one_mem := by
    intro vertex
    exact MvPolynomial.isHomogeneous_one T K
  mul_mem _ _ _ _ := graph.mul_mem_homogeneousPiece

/-- A named grading structure on polynomial splines with finitely many vertices. -/
@[instance_reducible]
noncomputable def gradedAlgebra [Fintype V] : GradedAlgebra graph.homogeneousPiece := by
  letI := graph.homogeneousPieceGradedMonoid
  exact (graph.homogeneousPiece_isInternal hlabels).gradedAlgebra

end Schubert.Splines.IdealLabeledGraph
