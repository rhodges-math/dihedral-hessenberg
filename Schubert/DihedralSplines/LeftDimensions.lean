import Schubert.FiniteGroupCharacters.RepresentationDimension
import Schubert.DihedralSplines.QuotientRepresentation
import Schubert.DihedralSplines.FlowupBasis
import Schubert.DihedralSplines.HessenbergLengthPolynomialClosed

/-! # Rank recovery from dimensions of the left quotient -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Left

open Schubert.Dihedral Schubert.FiniteGroupCharacters
open scoped BigOperators

private theorem cast_geometric (count : ℕ) :
    ((Polynomial.map (Nat.castRingHom ℂ)
      (∑ exponent ∈ Finset.range count, (Polynomial.X : Polynomial ℕ) ^ exponent)) :
        PowerSeries ℂ) =
      ∑ exponent ∈ Finset.range count, (PowerSeries.X : PowerSeries ℂ) ^ exponent := by
  change (Polynomial.coeToPowerSeries.ringHom.comp
    (Polynomial.mapRingHom (Nat.castRingHom ℂ))) _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  change ((Polynomial.map (Nat.castRingHom ℂ) (Polynomial.X ^ exponent)) :
    PowerSeries ℂ) = PowerSeries.X ^ exponent
  simp only [Polynomial.map_pow,
    Polynomial.map_X,
    Polynomial.coe_pow, Polynomial.coe_X]

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

omit [NeZero n] in
/-- Taking dimensions recovers the full rank polynomial of the left quotient. -/
theorem dimension_rank :
    PowerSeries.map (dimensionHom ℂ (DihedralGroup n))
      (RootSubset.Left.gradedClass ideal.toRootSubset hthree) =
        ((rankPolynomial ideal).map (Nat.castRingHom ℂ) : PowerSeries ℂ) := by
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Left.gradedClass, graded_dimension_coeff,
    Polynomial.coeff_coe, Polynomial.coeff_map, rankPolynomial_coeff]
  rfl

/-- The dimension series is the H-length generating polynomial. -/
theorem dimension_length :
    PowerSeries.map (dimensionHom ℂ (DihedralGroup n))
      (RootSubset.Left.gradedClass ideal.toRootSubset hthree) =
        (ideal.lengthPolynomial.map (Nat.castRingHom ℂ) : PowerSeries ℂ) := by
  rw [dimension_rank ideal, FlowupSpline.Left.rank_eq]

/-- Even root cardinality gives the displayed geometric rank term and middle correction. -/
theorem dimension_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half) :
    PowerSeries.map (dimensionHom ℂ (DihedralGroup n))
      (RootSubset.Left.gradedClass ideal.toRootSubset hthree) =
        (1 + PowerSeries.X) *
          (∑ exponent ∈ Finset.range (2 * half), (PowerSeries.X : PowerSeries ℂ) ^ exponent) +
        PowerSeries.C ((2 * n - 4 * half : ℕ) : ℂ) * PowerSeries.X ^ half := by
  rw [dimension_length ideal, ideal.lengthPolynomial_even half hcard]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_pow,
    cast_geometric]
  rfl

/-- Odd root cardinality gives the displayed pair of equal middle corrections. -/
theorem dimension_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1) :
    PowerSeries.map (dimensionHom ℂ (DihedralGroup n))
      (RootSubset.Left.gradedClass ideal.toRootSubset hthree) =
        (1 + PowerSeries.X) *
          (∑ exponent ∈ Finset.range (2 * half + 1),
            (PowerSeries.X : PowerSeries ℂ) ^ exponent) +
        PowerSeries.C ((n - 2 * half - 1 : ℕ) : ℂ) *
          (PowerSeries.X ^ half + PowerSeries.X ^ (half + 1)) := by
  rw [dimension_length ideal, ideal.lengthPolynomial_odd half hcard]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_one,
    Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_pow,
    cast_geometric]
  rfl

end Schubert.DihedralSplines.HessenbergIdeal.Left
