import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Order.WellFounded

/-! # Nondegeneracy from triangular bilinear evaluations -/

namespace Schubert.Splines

variable {K M N L I : Type*} [Field K]
variable [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
variable [AddCommGroup L] [Module K L]
variable [PartialOrder I] [WellFoundedLT I] [Fintype I]

/-- A triangular bilinear table with nonzero diagonal has no left kernel. -/
theorem pairing_left_nondegenerate (basis : Module.Basis I K M) (partner : I → N)
    (pairing : M →ₗ[K] N →ₗ[K] L)
    (hzero : ∀ first second, ¬ first ≤ second → pairing (basis first) (partner second) = 0)
    (hdiagonal : ∀ index, pairing (basis index) (partner index) ≠ 0)
    (value : M) (hvalue : ∀ index, pairing value (partner index) = 0) : value = 0 := by
  classical
  have hcoefficients : ∀ index, basis.repr value index = 0 := by
    intro index
    refine (wellFounded_lt : WellFounded ((· < ·) : I → I → Prop)).induction
      (C := fun index => basis.repr value index = 0) index ?_
    intro index ih
    have hsum := congrArg (fun vector => pairing vector (partner index)) (basis.sum_repr value)
    have hsumZero : ∑ other : I,
        basis.repr value other • pairing (basis other) (partner index) = 0 := by
      simpa only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        hvalue index] using hsum
    have hterms : ∀ other ∈ (Finset.univ : Finset I), other ≠ index →
        basis.repr value other • pairing (basis other) (partner index) = 0 := by
      intro other _ hne
      by_cases hle : other ≤ index
      · rw [ih other (lt_of_le_of_ne hle hne), zero_smul]
      · rw [hzero other index hle, smul_zero]
    rw [Finset.sum_eq_single index hterms (fun h => (h (Finset.mem_univ index)).elim)]
      at hsumZero
    exact (smul_eq_zero.mp hsumZero).resolve_right (hdiagonal index)
  apply basis.repr.injective
  ext index
  simpa only [map_zero, Finsupp.zero_apply] using hcoefficients index

end Schubert.Splines
