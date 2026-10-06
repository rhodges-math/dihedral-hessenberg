import Schubert.FiniteGroupCharacters.ShiftedSeries

/-! # Coefficients of the finite doubled geometric series -/

open scoped BigOperators
namespace Schubert.FiniteGroupCharacters

/-- The finite doubled geometric series has one endpoint and two interior coefficients. -/
theorem geometric_double_coeff {R : Type*} [CommSemiring R] (size degree : ℕ)
    (hpositive : 0 < size) :
    PowerSeries.coeff degree ((1 + PowerSeries.X) *
      ∑ exponent ∈ Finset.range size, (PowerSeries.X : PowerSeries R) ^ exponent) =
      if degree = 0 ∨ degree = size then 1 else if degree < size then 2 else 0 := by
  have hfirst : (∑ exponent ∈ Finset.range size,
      (PowerSeries.X : PowerSeries R) ^ exponent) =
      ∑ exponent ∈ Finset.range size, PowerSeries.monomial (0 + exponent) (1 : R) := by
    simp only [zero_add, PowerSeries.X_pow_eq]
  have hsecond : (PowerSeries.X : PowerSeries R) *
      (∑ exponent ∈ Finset.range size, PowerSeries.X ^ exponent) =
      ∑ exponent ∈ Finset.range size, PowerSeries.monomial (1 + exponent) (1 : R) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro exponent _
    rw [← pow_succ', PowerSeries.X_pow_eq, Nat.add_comm exponent 1]
  rw [add_mul, one_mul, hsecond, hfirst, map_add, shifted_sum_coeff, shifted_sum_coeff]
  split_ifs <;> norm_num <;> omega

end Schubert.FiniteGroupCharacters
