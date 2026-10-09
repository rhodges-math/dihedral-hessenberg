import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

/-! # Coefficients of a finite geometric sum -/

namespace Schubert.DihedralSplines

open scoped BigOperators

/-- A finite sum of consecutive monomials has coefficient one exactly in its range. -/
theorem geometric_coeff (size degree : ℕ) :
    (∑ exponent ∈ Finset.range size, (Polynomial.X : Polynomial ℕ) ^ exponent).coeff degree =
      if degree < size then 1 else 0 := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  simp

/-- Multiplying the geometric sum by one plus X gives unit endpoints and double interior. -/
theorem interval_coeff (size degree : ℕ) (hpositive : 0 < size) :
    ((1 + Polynomial.X) *
      ∑ exponent ∈ Finset.range size, (Polynomial.X : Polynomial ℕ) ^ exponent).coeff degree =
      if degree = 0 ∨ degree = size then 1 else if degree < size then 2 else 0 := by
  rw [add_mul, one_mul, Polynomial.coeff_add]
  cases degree with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero, geometric_coeff]
    simp [hpositive]
  | succ degree =>
    rw [Polynomial.coeff_X_mul, geometric_coeff, geometric_coeff]
    simp only [Nat.succ_ne_zero, false_or]
    split_ifs <;> simp_all <;> omega

/-- The even middle correction changes only the central coefficient. -/
theorem even_closed_coeff (n half degree : ℕ) (hpositive : 0 < half)
    (hbound : 2 * half ≤ n) :
    (((1 + Polynomial.X) *
      ∑ exponent ∈ Finset.range (2 * half), (Polynomial.X : Polynomial ℕ) ^ exponent) +
      Polynomial.C (2 * n - 4 * half) * Polynomial.X ^ half).coeff degree =
      if 2 * half < degree then 0 else
      if degree = 0 ∨ degree = 2 * half then 1 else
      if degree < half ∨ half < degree then 2 else 2 * n - 4 * half + 2 := by
  rw [Polynomial.coeff_add, interval_coeff _ _ (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> (try simp only [mul_zero, mul_one, zero_add, add_zero]) <;> omega

/-- The odd middle correction changes the two adjacent central coefficients. -/
theorem odd_closed_coeff (n half degree : ℕ) (hpositive : 0 < half)
    (hbound : 2 * half + 1 ≤ n) :
    (((1 + Polynomial.X) *
      ∑ exponent ∈ Finset.range (2 * half + 1), (Polynomial.X : Polynomial ℕ) ^ exponent) +
      Polynomial.C (n - 2 * half - 1) *
        (Polynomial.X ^ half + Polynomial.X ^ (half + 1))).coeff degree =
      if 2 * half + 1 < degree then 0 else
      if degree = 0 ∨ degree = 2 * half + 1 then 1 else
      if degree < half ∨ half + 1 < degree then 2 else n - 2 * half + 1 := by
  rw [Polynomial.coeff_add, interval_coeff _ _ (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_X_pow]
  split_ifs <;> (try simp only [mul_zero, mul_one, zero_add, add_zero]) <;> omega

end Schubert.DihedralSplines
