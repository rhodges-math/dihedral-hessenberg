import Schubert.Dihedral.CoinvariantDegreeSpans
import Schubert.Dihedral.CoinvariantRelations

/-! # Complementary-degree multiplication in the coinvariant algebra

Positive mixed axial powers vanish, while pure top powers remain nonzero. These
relations give nondegenerate multiplication between complementary middle degrees.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every positive mixed axial power vanishes in the official quotient. -/
theorem coinvariant_mixed_axial_pow_eq_zero (n : ℕ) [NeZero n] (first second : ℕ)
    (hfirst : 0 < first) (hsecond : 0 < second) :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ first *
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ second = 0 := by
  rw [show first = (first - 1) + 1 by omega, show second = (second - 1) + 1 by omega,
    pow_succ, pow_succ]
  calc
    _ = (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ (first - 1) *
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ (second - 1)) *
      (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU *
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV) := by ring
    _ = 0 := by rw [coinvariant_auxiliary_mul, mul_zero]

/-- The second top axial power is also nonzero. -/
theorem coinvariant_top_second_axial_ne_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ n ≠ 0 := by
  intro hzero
  have hrelation := coinvariant_top_relation n
  rw [hzero, mul_zero, add_zero] at hrelation
  exact coinvariant_top_axial_ne_zero n hthree (by simpa using hrelation)

/-- A nonzero middle-degree class has a nonzero product in the complementary degree. -/
theorem _root_.Schubert.Dihedral.Coinvariant.Middle.mul_nondegenerate (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) (degree : ℕ) (hpositive : 0 < degree) (hbelow : degree < n)
    (polynomial : CoinvariantAlgebra n)
    (hpolynomial : polynomial ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree)
    (hnonzero : polynomial ≠ 0) :
    ∃ complement : CoinvariantAlgebra n,
      complement ∈ TauCeti.GradedAlgebra.quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) (n - degree) ∧
      polynomial * complement ≠ 0 := by
  rw [_root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_middle n hthree degree hpositive hbelow]
    at hpolynomial
  obtain ⟨first, second, hcoefficients⟩ := Submodule.mem_span_pair.mp hpolynomial
  simp only [map_pow] at hcoefficients
  have hcomplement : 0 < n - degree := by omega
  have hdegree : degree + (n - degree) = n := by omega
  by_cases hfirst : first = 0
  · have hsecond : second ≠ 0 := by
      intro hzero
      simp [hfirst, hzero] at hcoefficients
      exact hnonzero hcoefficients.symm
    refine ⟨Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ (n - degree), ?_, ?_⟩
    · simpa using TauCeti.GradedAlgebra.mk_mem_quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
        (auxiliaryV_isHomogeneous.pow (n - degree))
    · rw [← hcoefficients]
      simp only [hfirst, zero_smul, zero_add, smul_mul_assoc, ← pow_add, hdegree]
      exact smul_ne_zero hsecond (coinvariant_top_second_axial_ne_zero n hthree)
  · refine ⟨Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ (n - degree), ?_, ?_⟩
    · simpa using TauCeti.GradedAlgebra.mk_mem_quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
        (auxiliaryU_isHomogeneous.pow (n - degree))
    · rw [← hcoefficients, add_mul, smul_mul_assoc, smul_mul_assoc]
      rw [mul_comm (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ degree),
        coinvariant_mixed_axial_pow_eq_zero n (n - degree) degree hcomplement hpositive,
        smul_zero, add_zero, ← pow_add, hdegree]
      exact smul_ne_zero hfirst (by simpa using coinvariant_top_axial_ne_zero n hthree)

/-- Multiplication into the top degree is nondegenerate in every coinvariant degree. -/
theorem coinvariant_multiplication_nondegenerate (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (hbound : degree ≤ n) (polynomial : CoinvariantAlgebra n)
    (hpolynomial : polynomial ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree)
    (hnonzero : polynomial ≠ 0) :
    ∃ complement : CoinvariantAlgebra n,
      complement ∈ TauCeti.GradedAlgebra.quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) (n - degree) ∧
      polynomial * complement ≠ 0 := by
  by_cases hzero : degree = 0
  · subst degree
    rw [_root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_zero n hthree] at hpolynomial
    obtain ⟨scalar, hscalar⟩ := Submodule.mem_span_singleton.mp hpolynomial
    have hscalar_ne : scalar ≠ 0 := by
      intro hequal
      simp [hequal] at hscalar
      exact hnonzero hscalar.symm
    refine ⟨Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n, ?_, ?_⟩
    · simpa using TauCeti.GradedAlgebra.mk_mem_quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
        (auxiliaryU_isHomogeneous.pow n)
    · rw [← hscalar, smul_mul_assoc, one_mul]
      exact smul_ne_zero hscalar_ne (by simpa using coinvariant_top_axial_ne_zero n hthree)
  · by_cases htop : degree = n
    · subst degree
      refine ⟨1, ?_, by simpa using hnonzero⟩
      simpa using TauCeti.GradedAlgebra.mk_mem_quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n)
        (MvPolynomial.isHomogeneous_one (Fin 2) ℂ)
    · exact _root_.Schubert.Dihedral.Coinvariant.Middle.mul_nondegenerate n hthree degree
        (by omega) (by omega) polynomial hpolynomial hnonzero

end Schubert.Dihedral
