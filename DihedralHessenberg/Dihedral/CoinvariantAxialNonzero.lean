import DihedralHessenberg.Dihedral.CoinvariantDuality

/-! # Nonvanishing axial classes through the top coinvariant degree

An axial power of degree at most n cannot vanish, because multiplication by its
complementary axial power gives the nonzero top class.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every first axial power through degree n is nonzero in the coinvariant algebra. -/
theorem coinvariant_auxiliaryU_pow_ne_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (hbound : degree ≤ n) :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ degree ≠ 0 := by
  intro hzero
  have htop : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n = 0 := by
    calc
      _ = Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ (degree + (n - degree)) :=
        congrArg (fun exponent => Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ exponent)
          (Nat.add_sub_of_le hbound).symm
      _ = 0 := by rw [pow_add, hzero, zero_mul]
  exact coinvariant_top_axial_ne_zero n hthree (by simpa using htop)

/-- Every second axial power through degree n is nonzero in the coinvariant algebra. -/
theorem coinvariant_auxiliaryV_pow_ne_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (hbound : degree ≤ n) :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ degree ≠ 0 := by
  intro hzero
  have htop : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ n = 0 := by
    calc
      _ = Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ (degree + (n - degree)) :=
        congrArg (fun exponent => Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ exponent)
          (Nat.add_sub_of_le hbound).symm
      _ = 0 := by rw [pow_add, hzero, zero_mul]
  exact coinvariant_top_second_axial_ne_zero n hthree htop

/-- A class below the top degree annihilated by both axial coordinates is zero. -/
theorem _root_.Schubert.Dihedral.Coinvariant.annihilated_below_top_eq_zero (n : ℕ) [NeZero n]
  (hthree : 3 ≤ n)
    (degree : ℕ) (hbelow : degree < n) (polynomial : CoinvariantAlgebra n)
    (hpolynomial : polynomial ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree)
    (hfirst : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU * polynomial = 0)
    (hsecond : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV * polynomial = 0) :
    polynomial = 0 := by
  by_cases hzero : degree = 0
  · subst degree
    rw [_root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_zero n hthree] at hpolynomial
    obtain ⟨scalar, hscalar⟩ := Submodule.mem_span_singleton.mp hpolynomial
    rw [← hscalar, mul_smul_comm, mul_one] at hfirst
    have hscalar_zero : scalar = 0 := (smul_eq_zero.mp hfirst).resolve_right
      (by simpa using coinvariant_auxiliaryU_pow_ne_zero n hthree 1 (by omega))
    simpa [hscalar_zero] using hscalar.symm
  · have hpositive : 0 < degree := by omega
    rw [_root_.Schubert.Dihedral.Coinvariant.Piece.eq_span_middle n hthree degree hpositive hbelow]
      at hpolynomial
    obtain ⟨first, second, hcoefficients⟩ := Submodule.mem_span_pair.mp hpolynomial
    simp only [map_pow] at hcoefficients
    have hfirst_mixed : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU *
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ degree = 0 := by
      simpa using coinvariant_mixed_axial_pow_eq_zero n 1 degree (by omega) hpositive
    have hsecond_mixed : Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV *
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ degree = 0 := by
      rw [mul_comm]
      simpa using coinvariant_mixed_axial_pow_eq_zero n degree 1 hpositive (by omega)
    rw [← hcoefficients, mul_add, mul_smul_comm, mul_smul_comm, hfirst_mixed,
      smul_zero, add_zero, ← pow_succ'] at hfirst
    rw [← hcoefficients, mul_add, mul_smul_comm, mul_smul_comm, hsecond_mixed,
      smul_zero, zero_add, ← pow_succ'] at hsecond
    have hfirst_zero : first = 0 := (smul_eq_zero.mp hfirst).resolve_right
      (coinvariant_auxiliaryU_pow_ne_zero n hthree (degree + 1) (by omega))
    have hsecond_zero : second = 0 := (smul_eq_zero.mp hsecond).resolve_right
      (coinvariant_auxiliaryV_pow_ne_zero n hthree (degree + 1) (by omega))
    simpa [hfirst_zero, hsecond_zero] using hcoefficients.symm

/-- Both axial coordinates annihilate every top-degree coinvariant class. -/
theorem coinvariant_top_annihilated (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoinvariantAlgebra n)
    (hpolynomial : polynomial ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) n) :
    Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU * polynomial = 0 ∧
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV * polynomial = 0 := by
  rw [coinvariant_homogeneousPiece_eq_span_top n hthree] at hpolynomial
  obtain ⟨scalar, hscalar⟩ := Submodule.mem_span_singleton.mp hpolynomial
  simp only [map_pow] at hscalar
  constructor
  · rw [← hscalar, mul_smul_comm, ← pow_succ', coinvariant_auxiliaryU_pow_succ, smul_zero]
  · rw [← hscalar, mul_smul_comm, mul_comm]
    have hmixed := coinvariant_mixed_axial_pow_eq_zero n n 1 (by omega) (by omega)
    simpa using congrArg (fun value => scalar • value) hmixed

/-- Among nonzero homogeneous classes, joint coordinate annihilation detects the top degree. -/
theorem _root_.Schubert.Dihedral.Coinvariant.annihilated_iff_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (degree : ℕ) (polynomial : CoinvariantAlgebra n)
    (hpolynomial : polynomial ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree)
    (hnonzero : polynomial ≠ 0) :
    (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU * polynomial = 0 ∧
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV * polynomial = 0) ↔ degree = n := by
  constructor
  · intro hannihilated
    have hbound : degree ≤ n := by
      by_contra hnot
      have hbottom := _root_.Schubert.Dihedral.Coinvariant.Piece.eq_bot_above n hthree degree (by
        omega)
      rw [hbottom] at hpolynomial
      exact hnonzero hpolynomial
    by_contra hne
    exact hnonzero (_root_.Schubert.Dihedral.Coinvariant.annihilated_below_top_eq_zero n hthree
      degree (by omega)
      polynomial hpolynomial hannihilated.1 hannihilated.2)
  · intro htop
    subst degree
    exact coinvariant_top_annihilated n hthree polynomial hpolynomial

end Schubert.Dihedral
