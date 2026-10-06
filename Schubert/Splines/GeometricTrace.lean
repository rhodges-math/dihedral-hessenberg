import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Finite paired eigenvalue trace polynomials -/

namespace Schubert.Splines
open scoped BigOperators

/-- A paired root-of-unity geometric trace has the quadratic determinant numerator. -/
theorem paired_trace_identity {R : Type*} [CommRing R] (n : ℕ) (a b : R)
    (hab : a * b = 1) (ha : a ^ n = 1) (hb : b ^ n = 1) :
    (1 - Polynomial.C a * Polynomial.X) * (1 - Polynomial.C b * Polynomial.X) *
      ((∑ degree ∈ Finset.range n, (Polynomial.C a * Polynomial.X) ^ degree) +
        (∑ degree ∈ Finset.range n, (Polynomial.C b * Polynomial.X) ^ degree) -
        1 + Polynomial.X ^ n) =
      (1 - Polynomial.X ^ 2) * (1 - Polynomial.X ^ n) := by
  have hfirst := mul_neg_geom_sum (Polynomial.C a * Polynomial.X) n
  have hsecond := mul_neg_geom_sum (Polynomial.C b * Polynomial.X) n
  simp only [mul_pow, ← map_pow, ha, hb, map_one, one_mul] at hfirst hsecond
  have hproduct : (Polynomial.C a * Polynomial.X) *
      (Polynomial.C b * Polynomial.X) = (Polynomial.X : Polynomial R) ^ 2 := by
    calc
      _ = Polynomial.C (a * b) * Polynomial.X ^ 2 := by rw [map_mul]; ring
      _ = _ := by rw [hab, map_one, one_mul]
  simp only [mul_pow, ← map_pow]
  linear_combination (1 - Polynomial.C b * Polynomial.X) * hfirst +
    (1 - Polynomial.C a * Polynomial.X) * hsecond -
    (1 - Polynomial.X ^ n) * hproduct

end Schubert.Splines
