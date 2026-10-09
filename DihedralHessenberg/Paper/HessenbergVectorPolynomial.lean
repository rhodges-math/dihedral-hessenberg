import DihedralHessenberg.Paper.HessenbergObjectBridge
import DihedralHessenberg.Paper.HessenbergPolynomial

/-! # The length generating polynomial of a vector Hessenberg ideal -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- Each element contributes a monomial with exponent its H-inversion cardinality. -/
def lengthPolynomial (ideal : HessenbergIdeal n hthree) : Polynomial ℕ :=
  ∑ element : DihedralGroup n, (Polynomial.X : Polynomial ℕ) ^ ideal.toRootSubset.length element

/-- Vector transport preserves the length generating polynomial exactly. -/
theorem lengthPolynomial_indexed (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial = ideal.indexed.lengthPolynomial := by
  unfold lengthPolynomial HessenbergSpace.lengthPolynomial
  apply Finset.sum_congr rfl
  intro element _
  rw [ideal.length_indexed]

/-- Each coefficient counts elements with that H-inversion cardinality. -/
theorem coeff (ideal : HessenbergIdeal n hthree) (degree : ℕ) :
    ideal.lengthPolynomial.coeff degree =
      (Finset.univ.filter fun element : DihedralGroup n =>
        ideal.toRootSubset.length element = degree).card := by
  classical
  rw [ideal.lengthPolynomial_indexed, ideal.indexed.lengthPolynomial_coeff]
  congr 1
  ext element
  rw [Finset.mem_filter, Finset.mem_filter, ideal.length_indexed]

/-- The generating polynomial has constant coefficient one. -/
theorem coeff_zero (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial.coeff 0 = 1 := by
  rw [ideal.lengthPolynomial_indexed, ideal.indexed.lengthPolynomial_coeff_zero]

/-- The coefficient at the selected-root cardinality is one. -/
theorem coeff_top (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial.coeff ideal.carrier.ncard = 1 := by
  rw [ideal.lengthPolynomial_indexed, ideal.ncard_indexed,
    ideal.indexed.lengthPolynomial_coeff_card_roots]

/-- All coefficients beyond the selected-root cardinality vanish. -/
theorem coeff_above (ideal : HessenbergIdeal n hthree) (degree : ℕ)
    (hdegree : ideal.carrier.ncard < degree) : ideal.lengthPolynomial.coeff degree = 0 := by
  rw [ideal.lengthPolynomial_indexed]
  exact ideal.indexed.lengthPolynomial_coeff_above_card degree
    (by simpa only [ideal.ncard_indexed] using hdegree)

/-- Complementary coefficients about the selected-root cardinality coincide. -/
theorem coeff_complement (ideal : HessenbergIdeal n hthree) (degree : ℕ)
    (hdegree : degree ≤ ideal.carrier.ncard) :
    ideal.lengthPolynomial.coeff degree =
      ideal.lengthPolynomial.coeff (ideal.carrier.ncard - degree) := by
  rw [ideal.lengthPolynomial_indexed, ideal.ncard_indexed]
  exact ideal.indexed.lengthPolynomial_coeff_complementary degree
    (by simpa only [ideal.ncard_indexed] using hdegree)

/-- The sum of coefficients is the order of the dihedral group. -/
theorem eval_one (ideal : HessenbergIdeal n hthree) :
    ideal.lengthPolynomial.eval 1 = 2 * n := by
  rw [ideal.lengthPolynomial_indexed, ideal.indexed.lengthPolynomial_eval_one]

end Schubert.DihedralSplines.HessenbergIdeal
