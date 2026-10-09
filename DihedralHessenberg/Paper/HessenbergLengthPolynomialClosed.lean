import DihedralHessenberg.Paper.HessenbergVectorPolynomial
import DihedralHessenberg.Paper.HessenbergMultiplicity
import DihedralHessenberg.Paper.GeometricCoeff

/-! # Closed length generating polynomials -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- Length fibers give endpoint, outer, and middle coefficients. -/
theorem coeff_piecewise (ideal : HessenbergIdeal n hthree) (degree : ℕ) :
    ideal.lengthPolynomial.coeff degree =
      if ideal.carrier.ncard < degree then 0 else
      if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else
      if degree < ideal.carrier.ncard / 2 ∨
        ideal.carrier.ncard - ideal.carrier.ncard / 2 < degree then 2 else
      if Even ideal.carrier.ncard then 2 * n - 2 * ideal.carrier.ncard + 2
        else n - ideal.carrier.ncard + 2 := by
  rw [ideal.coeff]
  simp_rw [ideal.length_indexed]
  rw [ideal.indexed.card_length_eq_piecewise, ← ideal.ncard_indexed]

/-- An even root cardinality produces a single central correction to the geometric sum. -/
theorem lengthPolynomial_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) :
    ideal.lengthPolynomial =
      (1 + Polynomial.X) *
        (∑ exponent ∈ Finset.range (2 * half), (Polynomial.X : Polynomial ℕ) ^ exponent) +
      Polynomial.C (2 * n - 4 * half) * Polynomial.X ^ half := by
  have hminimum := ideal.indexed.two_le_card
  have hmaximum := ideal.indexed.card_le
  rw [← ideal.ncard_indexed, hcard] at hminimum hmaximum
  have heven : Even (2 * half) := ⟨half, by omega⟩
  apply Polynomial.ext
  intro degree
  rw [ideal.coeff_piecewise, hcard,
    even_closed_coeff n half degree (by omega) hmaximum]
  have hhalf : 2 * half / 2 = half := by omega
  rw [hhalf, ite_eq_left heven]
  split_ifs <;> omega

/-- An odd root cardinality produces equal corrections at the two middle degrees. -/
theorem lengthPolynomial_odd (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) :
    ideal.lengthPolynomial =
      (1 + Polynomial.X) *
        (∑ exponent ∈ Finset.range (2 * half + 1), (Polynomial.X : Polynomial ℕ) ^ exponent) +
      Polynomial.C (n - 2 * half - 1) *
        (Polynomial.X ^ half + Polynomial.X ^ (half + 1)) := by
  have hminimum := ideal.indexed.two_le_card
  have hmaximum := ideal.indexed.card_le
  rw [← ideal.ncard_indexed, hcard] at hminimum hmaximum
  have hodd : ¬Even (2 * half + 1) := by rw [Nat.even_iff]; omega
  apply Polynomial.ext
  intro degree
  rw [ideal.coeff_piecewise, hcard,
    odd_closed_coeff n half degree (by omega) hmaximum]
  have hhalf : (2 * half + 1) / 2 = half := by omega
  rw [hhalf, ite_eq_right hodd]
  split_ifs <;> omega

end Schubert.DihedralSplines.HessenbergIdeal
