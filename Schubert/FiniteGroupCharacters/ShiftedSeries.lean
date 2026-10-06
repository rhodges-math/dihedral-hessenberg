import Mathlib.RingTheory.PowerSeries.Basic
import Lean.Elab.Tactic.Omega

/-! # Coefficients of finite shifted class series -/

open scoped BigOperators

namespace Schubert.FiniteGroupCharacters

/-- A finite shifted monomial sum has precisely its indexed coefficients in its degree interval. -/
theorem shifted_sum_coeff {R : Type*} [CommSemiring R] (shift count degree : ℕ)
    (coefficient : ℕ → R) :
    PowerSeries.coeff degree
      (∑ index ∈ Finset.range count, PowerSeries.monomial (shift + index) (coefficient index)) =
        if shift ≤ degree ∧ degree < shift + count then coefficient (degree - shift) else 0 := by
  classical
  rw [map_sum]
  by_cases hinterval : shift ≤ degree ∧ degree < shift + count
  · rw [ite_eq_left hinterval]
    rw [Finset.sum_eq_single (degree - shift)]
    · rw [PowerSeries.coeff_monomial, ite_eq_left (show degree = shift + (degree - shift)
        by omega)]
    · intro index _ hne
      rw [PowerSeries.coeff_monomial, ite_eq_right (show degree ≠ shift + index by omega)]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr (by omega)))
  · rw [ite_eq_right hinterval]
    apply Finset.sum_eq_zero
    intro index hindex
    have hindex' := Finset.mem_range.mp hindex
    rw [PowerSeries.coeff_monomial, ite_eq_right (show degree ≠ shift + index by omega)]

end Schubert.FiniteGroupCharacters
