import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Order.Minimal
import Schubert.Splines.TriangularIndependence

/-! # Bases from triangular spline families

Successive elimination at minimal remaining vertices expresses every spline in a
triangular family, provided each diagonal divides the possible value of a spline
vanishing below that vertex. Nonzero diagonal entries give linear independence over a domain.
-/

namespace Schubert.Splines.IdealLabeledGraph

universe u v w

variable {R : Type u} {V : Type v} {E : Type w}
variable [CommRing R] [PartialOrder V] [WellFoundedLT V] [Fintype V]
variable (graph : IdealLabeledGraph R V E)

/-- A triangular family spans when each diagonal divides residual values at its vertex. -/
theorem span_eq_top_of_triangular (family : V → graph.Spline)
    (hsupport : ∀ first second, ¬ first ≤ second → (family first : V → R) second = 0)
    (hdivides : ∀ (value : graph.Spline) vertex,
      (∀ lower, lower < vertex → (value : V → R) lower = 0) →
        (family vertex : V → R) vertex ∣ (value : V → R) vertex) :
    Submodule.span R (Set.range family) = ⊤ := by
  classical
  have hspanning (remaining : Finset V) :
      (∀ first second, first ∈ remaining → first ≤ second → second ∈ remaining) →
      ∀ value : graph.Spline, (∀ vertex, vertex ∉ remaining → (value : V → R) vertex = 0) →
        value ∈ Submodule.span R (Set.range family) := by
    refine Finset.strongInductionOn remaining ?_
    intro remaining ih hupper value hzero
    by_cases hempty : remaining = ∅
    · subst remaining
      have hvalue : value = 0 := graph.spline_ext fun vertex =>
        hzero vertex (by simp)
      rw [hvalue]
      exact Submodule.zero_mem _
    · obtain ⟨vertex, hminimal⟩ := exists_minimal_of_wellFoundedLT
        (fun vertex : V => vertex ∈ remaining) (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hlower : ∀ lower, lower < vertex → (value : V → R) lower = 0 := by
        intro lower hlt
        apply hzero
        intro hmem
        exact (not_le_of_gt hlt) (hminimal.le_of_le hmem hlt.le)
      obtain ⟨coefficient, hcoefficient⟩ := hdivides value vertex hlower
      have hupperErase : ∀ first second, first ∈ remaining.erase vertex →
          first ≤ second → second ∈ remaining.erase vertex := by
        intro first second hfirst hle
        refine Finset.mem_erase.mpr ⟨?_, hupper first second (Finset.mem_erase.mp hfirst).2 hle⟩
        intro heq
        subst second
        have hback := hminimal.le_of_le (Finset.mem_erase.mp hfirst).2 hle
        exact (Finset.mem_erase.mp hfirst).1 (le_antisymm hle hback)
      have hzeroResidual : ∀ other, other ∉ remaining.erase vertex →
          ((value - coefficient • family vertex : graph.Spline) : V → R) other = 0 := by
        intro other hother
        by_cases heq : other = vertex
        · subst other
          change (value : V → R) vertex - coefficient * (family vertex : V → R) vertex = 0
          rw [hcoefficient, mul_comm, sub_self]
        · have houtside : other ∉ remaining := by
            intro hmem
            exact hother (Finset.mem_erase.mpr ⟨heq, hmem⟩)
          have hfamily : (family vertex : V → R) other = 0 := by
            apply hsupport
            intro hle
            exact houtside (hupper vertex other hminimal.prop hle)
          change (value : V → R) other - coefficient * (family vertex : V → R) other = 0
          rw [hzero other houtside, hfamily, mul_zero, sub_self]
      have hresidual := ih (remaining.erase vertex) (Finset.erase_ssubset hminimal.prop)
        hupperErase (value - coefficient • family vertex) hzeroResidual
      have hterm : coefficient • family vertex ∈ Submodule.span R (Set.range family) :=
        Submodule.smul_mem _ coefficient (Submodule.subset_span ⟨vertex, rfl⟩)
      simpa only [sub_add_cancel] using
        (Submodule.span R (Set.range family)).add_mem hresidual hterm
  apply top_unique
  intro value _
  exact hspanning Finset.univ (fun _ _ _ _ => Finset.mem_univ _) value
    (fun vertex hnot => (hnot (Finset.mem_univ vertex)).elim)

/-- A triangular spline family with nonzero diagonal and residual divisibility is a basis. -/
noncomputable def triangularBasis [IsDomain R] (family : V → graph.Spline)
    (hsupport : ∀ first second, ¬ first ≤ second → (family first : V → R) second = 0)
    (hdiagonal : ∀ vertex, (family vertex : V → R) vertex ≠ 0)
    (hdivides : ∀ (value : graph.Spline) vertex,
      (∀ lower, lower < vertex → (value : V → R) lower = 0) →
        (family vertex : V → R) vertex ∣ (value : V → R) vertex) :
    Module.Basis V R graph.Spline :=
  Module.Basis.mk (graph.linearIndependent_of_triangular family hsupport hdiagonal)
    (graph.span_eq_top_of_triangular family hsupport hdivides).ge

/-- The basis constructed from a triangular family has exactly the given basis vectors. -/
theorem triangularBasis_apply [IsDomain R] (family : V → graph.Spline)
    (hsupport : ∀ first second, ¬ first ≤ second → (family first : V → R) second = 0)
    (hdiagonal : ∀ vertex, (family vertex : V → R) vertex ≠ 0)
    (hdivides : ∀ (value : graph.Spline) vertex,
      (∀ lower, lower < vertex → (value : V → R) lower = 0) →
        (family vertex : V → R) vertex ∣ (value : V → R) vertex)
    (vertex : V) :
    graph.triangularBasis family hsupport hdiagonal hdivides vertex = family vertex :=
  Module.Basis.mk_apply _ _ vertex

end Schubert.Splines.IdealLabeledGraph
