import DihedralHessenberg.Paper.HessenbergLengthFibers
import DihedralHessenberg.Paper.HessenbergDegreeCount
import Mathlib.Algebra.Polynomial.BigOperators

/-! # The Hessenberg length generating polynomial

Each vertex contributes one monomial whose exponent is its H-length.
The coefficients count H-degree fibers.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- The paper's H-length generating polynomial with natural number coefficients. -/
noncomputable def lengthPolynomial (ideal : HessenbergSpace n hthree) : Polynomial ℕ :=
  ∑ element : DihedralGroup n, (Polynomial.X : Polynomial ℕ) ^ ideal.length element

/-- A coefficient of the generating polynomial counts vertices of that H-degree. -/
theorem lengthPolynomial_coeff (ideal : HessenbergSpace n hthree) (degree : ℕ) :
    ideal.lengthPolynomial.coeff degree =
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = degree).card := by
  classical
  rw [lengthPolynomial, Polynomial.finsetSum_coeff, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [Polynomial.coeff_X_pow, eq_comm]

/-- The constant coefficient of the H-length polynomial is one. -/
theorem lengthPolynomial_coeff_zero (ideal : HessenbergSpace n hthree) :
    ideal.lengthPolynomial.coeff 0 = 1 := by
  rw [ideal.lengthPolynomial_coeff, ideal.card_length_eq_zero]

/-- The coefficient in degree |H| of the H-length polynomial is one. -/
theorem lengthPolynomial_coeff_card_roots (ideal : HessenbergSpace n hthree) :
    ideal.lengthPolynomial.coeff ideal.roots.card = 1 := by
  rw [ideal.lengthPolynomial_coeff, ideal.card_length_eq_card_roots]

/-- All coefficients above |H| vanish. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.lengthPolynomial_coeff_above_card (ideal :
  HessenbergSpace n hthree)
    (degree : ℕ) (hdegree : ideal.roots.card < degree) :
    ideal.lengthPolynomial.coeff degree = 0 := by
  classical
  rw [ideal.lengthPolynomial_coeff]
  have hempty : (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.length element = degree) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro element hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hbound := ideal.length_le_card_roots element
    omega
  rw [hempty, Finset.card_empty]

/-- Complementary coefficients of the H-length generating polynomial are equal. -/
theorem lengthPolynomial_coeff_complementary (ideal : HessenbergSpace n hthree)
    (degree : ℕ) (hdegree : degree ≤ ideal.roots.card) :
    ideal.lengthPolynomial.coeff degree =
      ideal.lengthPolynomial.coeff (ideal.roots.card - degree) := by
  rw [ideal.lengthPolynomial_coeff, ideal.lengthPolynomial_coeff]
  exact ideal.card_length_eq_card_complementary_length degree hdegree

/-- The sum of coefficients of the H-length generating polynomial is 2n. -/
theorem lengthPolynomial_eval_one (ideal : HessenbergSpace n hthree) :
    ideal.lengthPolynomial.eval 1 = 2 * n := by
  classical
  rw [lengthPolynomial, Polynomial.eval_finsetSum]
  simp [DihedralGroup.card]

end Schubert.DihedralSplines.HessenbergSpace
