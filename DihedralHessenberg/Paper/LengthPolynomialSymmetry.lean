import DihedralHessenberg.Paper.HessenbergVectorPolynomial
import Mathlib.Algebra.Polynomial.Reverse

/-! # Degree and reversal of the selected-root length polynomial -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- The degree of the length polynomial is the selected-root cardinality. -/
theorem lengthPolynomial_natDegree (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial.natDegree = ideal.carrier.ncard := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (ideal.coeff_above)
  · rw [ideal.coeff_top]
    exact one_ne_zero

/-- Reversing all coefficients preserves the length polynomial. -/
theorem lengthPolynomial_reverse (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial.reverse = ideal.lengthPolynomial := by
  ext degree
  rw [Polynomial.coeff_reverse, ideal.lengthPolynomial_natDegree]
  by_cases hdegree : degree ≤ ideal.carrier.ncard
  · rw [Polynomial.revAt_le hdegree]
    exact (ideal.coeff_complement degree hdegree).symm
  · rw [Polynomial.revAt_eq_self_of_lt (Nat.lt_of_not_ge hdegree)]

end Schubert.DihedralSplines.HessenbergIdeal
