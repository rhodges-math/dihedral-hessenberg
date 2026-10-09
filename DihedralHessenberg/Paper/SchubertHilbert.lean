import DihedralHessenberg.Paper.SchubertBasis
import DihedralHessenberg.Paper.FlowupHilbert
import DihedralHessenberg.Paper.HessenbergLengthPolynomialClosed

/-! # The full Schubert spline Hilbert series -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral
open scoped BigOperators

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- The full-root rank polynomial is the canonical length-generating sum. -/
theorem length_sum : (HessenbergIdeal.full n hthree).lengthPolynomial =
    ∑ vertex : DihedralGroup n, (Polynomial.X : Polynomial ℕ) ^ length n hthree vertex := by
  unfold HessenbergIdeal.lengthPolynomial
  apply Finset.sum_congr rfl
  intro vertex _
  change Polynomial.X ^ (RootSubset.full n).length vertex = _
  rw [RootSubset.length_full n hthree vertex]

/-- The canonical length-generating sum has the exact displayed finite geometric factorization. -/
theorem length_factor : (HessenbergIdeal.full n hthree).lengthPolynomial =
    (1 + Polynomial.X) * ∑ exponent ∈ Finset.range n, (Polynomial.X : Polynomial ℕ) ^ exponent :=
  by
  have hcard : (HessenbergIdeal.full n hthree).carrier.ncard = n := by
    rw [← (HessenbergIdeal.full n hthree).length_top]
    change (RootSubset.full n).length (longestElement n hthree) = n
    rw [RootSubset.length_full]
    exact (length_eq_longest n hthree _).mpr rfl
  rcases Nat.even_or_odd n with heven | hodd
  · obtain ⟨half, hhalf⟩ := heven
    have hformula := (HessenbergIdeal.full n hthree).lengthPolynomial_even half (by omega)
    have hzero : 2 * n - 4 * half = 0 := by omega
    have hsize : 2 * half = n := by omega
    simpa only [hzero, Polynomial.C_0, zero_mul, add_zero, hsize] using hformula
  · obtain ⟨half, hhalf⟩ := hodd
    have hformula := (HessenbergIdeal.full n hthree).lengthPolynomial_odd half (by omega)
    have hzero : n - 2 * half - 1 = 0 := by omega
    have hsize : 2 * half + 1 = n := by omega
    simpa only [hzero, Polynomial.C_0, zero_mul, add_zero, hsize] using hformula

/-- Every homogeneous dimension occurs in the full displayed Schubert Hilbert formula. -/
theorem hilbert_formula : (HessenbergIdeal.full n hthree).hilbertSeries =
    (((1 + Polynomial.X) *
      ∑ exponent ∈ Finset.range n, (Polynomial.X : Polynomial ℕ) ^ exponent).map
        (Nat.castRingHom ℚ) : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ 2).val := by
  rw [(HessenbergIdeal.full n hthree).hilbertSeries_formula, length_factor]

end Schubert.DihedralSplines.SchubertSpline
