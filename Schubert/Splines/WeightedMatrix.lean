import Mathlib.Data.Matrix.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Lean.Elab.Tactic.Omega

/-! # Invertible basis changes with strictly decreasing degree weights -/

namespace Schubert.Splines

/-- Powers of a strictly weight-decreasing matrix vanish outside the possible weight gap. -/
theorem weighted_matrix_pow_zero {R I : Type*} [Semiring R] [Fintype I] [DecidableEq I]
    (weights : I → ℕ) (matrix : Matrix I I R)
    (hdecrease : ∀ first second, weights second ≤ weights first → matrix first second = 0)
    (power : ℕ) (first second : I) (hgap : weights second < weights first + power) :
    (matrix ^ power) first second = 0 := by
  induction power generalizing first second with
  | zero =>
      have hne : first ≠ second := by intro heq; subst second; omega
      simp [hne]
  | succ power ih =>
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro middle _
      by_cases hleft : weights middle < weights first + power
      · rw [ih first middle hleft, zero_mul]
      · rw [hdecrease middle second (by omega), mul_zero]

/-- A finite matrix strictly decreasing bounded degree weights is nilpotent. -/
theorem weighted_matrix_nilpotent {R I : Type*} [Semiring R] [Fintype I] [DecidableEq I]
    (weights : I → ℕ) (matrix : Matrix I I R)
    (hdecrease : ∀ first second, weights second ≤ weights first → matrix first second = 0)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) : IsNilpotent matrix := by
  refine ⟨bound + 1, ?_⟩
  ext first second
  exact weighted_matrix_pow_zero weights matrix hdecrease _ first second (by
    have := hbound second
    omega)

/-- Adding a strictly weight-decreasing matrix to the identity gives an invertible basis change. -/
theorem weighted_matrix_unit {R I : Type*} [Ring R] [Fintype I] [DecidableEq I]
    (weights : I → ℕ) (matrix : Matrix I I R)
    (hdecrease : ∀ first second, weights second ≤ weights first → matrix first second = 0)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) : IsUnit (1 + matrix) :=
  (weighted_matrix_nilpotent weights matrix hdecrease bound hbound).isUnit_one_add

end Schubert.Splines
