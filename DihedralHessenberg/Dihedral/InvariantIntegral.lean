import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import DihedralHessenberg.Dihedral.CoinvariantFinite

/-! # Integral auxiliary coordinates over the invariant algebra

The nth powers of u and the signed nth power of v have invariant sum and product.
A monic quadratic equation therefore makes the auxiliary coordinates integral over
the official invariant algebra.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Two elements whose sum and product lie in a subalgebra are integral over it. -/
theorem isIntegral_of_sum_mul_mem_subalgebra {field algebra : Type*}
    [CommRing field] [CommRing algebra] [Algebra field algebra]
    (subalgebra : Subalgebra field algebra) (first second : algebra)
    (hsum : first + second ∈ subalgebra) (hproduct : first * second ∈ subalgebra) :
    IsIntegral subalgebra first := by
  refine ⟨Polynomial.X ^ 2 -
    (Polynomial.C ⟨first + second, hsum⟩ * Polynomial.X -
      Polynomial.C ⟨first * second, hproduct⟩), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    apply lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
    apply max_lt
    · calc
        (Polynomial.C (⟨first + second, hsum⟩ : subalgebra) * Polynomial.X).degree ≤
            (Polynomial.C (⟨first + second, hsum⟩ : subalgebra)).degree +
              Polynomial.X.degree := Polynomial.degree_mul_le _ _
        _ ≤ 1 := by
          have hbound := add_le_add
            (Polynomial.degree_C_le (a := (⟨first + second, hsum⟩ : subalgebra)))
            (Polynomial.degree_X_le (R := subalgebra))
          simpa only [zero_add] using hbound
        _ < 2 := by norm_num
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    change first ^ 2 - ((first + second) * first - first * second) = 0
    ring

/-- The first auxiliary coordinate is integral over the official invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.u_integral (n : ℕ) [NeZero n] :
    IsIntegral (invariantSubalgebra n) auxiliaryU := by
  have hsum : auxiliaryU ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryV ^ n ∈
      invariantSubalgebra n := higherInvariant_mem_invariantSubalgebra n
  have hproduct : auxiliaryU ^ n *
      (MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryV ^ n) ∈ invariantSubalgebra n := by
    have hequal : auxiliaryU ^ n * (MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryV ^ n) =
        MvPolynomial.C ((-1 : ℂ) ^ n) * quadraticInvariant ^ n := by
      rw [quadraticInvariant, mul_pow]
      ring
    rw [hequal]
    exact (invariantSubalgebra n).mul_mem ((invariantSubalgebra n).algebraMap_mem _)
      ((invariantSubalgebra n).pow_mem (_root_.Schubert.Dihedral.Invariants.F2.mem n) n)
  exact IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne n))
    (isIntegral_of_sum_mul_mem_subalgebra (invariantSubalgebra n) _ _ hsum hproduct)

/-- The second auxiliary coordinate is integral over the official invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.v_integral (n : ℕ) [NeZero n] :
    IsIntegral (invariantSubalgebra n) auxiliaryV := by
  have hsum : auxiliaryV ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryU ^ n ∈
      invariantSubalgebra n := by
    have hequal : auxiliaryV ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryU ^ n =
        MvPolynomial.C ((-1 : ℂ) ^ n) * higherInvariant n := by
      rw [higherInvariant]
      linear_combination -auxiliaryV ^ n * higherInvariant_sign_sq n
    rw [hequal]
    exact (invariantSubalgebra n).mul_mem ((invariantSubalgebra n).algebraMap_mem _)
      (higherInvariant_mem_invariantSubalgebra n)
  have hproduct : auxiliaryV ^ n *
      (MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryU ^ n) ∈ invariantSubalgebra n := by
    have hequal : auxiliaryV ^ n * (MvPolynomial.C ((-1 : ℂ) ^ n) * auxiliaryU ^ n) =
        MvPolynomial.C ((-1 : ℂ) ^ n) * quadraticInvariant ^ n := by
      rw [quadraticInvariant, mul_pow]
      ring
    rw [hequal]
    exact (invariantSubalgebra n).mul_mem ((invariantSubalgebra n).algebraMap_mem _)
      ((invariantSubalgebra n).pow_mem (_root_.Schubert.Dihedral.Invariants.F2.mem n) n)
  exact IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne n))
    (isIntegral_of_sum_mul_mem_subalgebra (invariantSubalgebra n) _ _ hsum hproduct)

set_option maxHeartbeats 2000000 in
/-- The auxiliary coordinates generate the polynomial algebra over its invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.adjoin_axial_eq_top (n : ℕ) [NeZero n] :
    Algebra.adjoin (invariantSubalgebra n)
      ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial) = ⊤ := by
  have hle : Algebra.adjoin ℂ ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial) ≤
      (Algebra.adjoin (invariantSubalgebra n)
        ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    intro polynomial hpolynomial
    change polynomial ∈ Algebra.adjoin (invariantSubalgebra n)
      ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial)
    exact Algebra.subset_adjoin (R := invariantSubalgebra n) hpolynomial
  rw [auxiliaryCoordinate_adjoin_eq_top] at hle
  apply top_unique
  intro polynomial hpolynomial
  exact hle hpolynomial

/-- The coordinate polynomial algebra is finite as a module over its invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.polynomial_finite (n : ℕ) [NeZero n] :
    Module.Finite (invariantSubalgebra n) CoordinatePolynomial := by
  have hintegral : ∀ polynomial ∈ ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial),
      IsIntegral (invariantSubalgebra n) polynomial := by
    intro polynomial hpolynomial
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hpolynomial
    rcases hpolynomial with rfl | rfl
    · exact _root_.Schubert.Dihedral.Invariants.u_integral n
    · exact _root_.Schubert.Dihedral.Invariants.v_integral n
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.toFinite _) hintegral
  rw [_root_.Schubert.Dihedral.Invariants.adjoin_axial_eq_top] at hfinite
  have := hfinite
  exact Module.Finite.of_surjective (Subalgebra.topEquiv.toLinearMap)
    Subalgebra.topEquiv.surjective

end Schubert.Dihedral
