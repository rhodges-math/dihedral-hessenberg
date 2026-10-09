import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import DihedralHessenberg.Dihedral.CoinvariantPowerRelations

/-! # Finite-dimensionality of the dihedral coinvariant algebra

The auxiliary coordinates generate the official polynomial algebra. Their nilpotent
images generate its coinvariant quotient, which is therefore finite-dimensional.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The auxiliary coordinates generate the official polynomial algebra. -/
theorem auxiliaryCoordinate_adjoin_eq_top :
    Algebra.adjoin ℂ ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial) = ⊤ := by
  apply top_unique
  intro polynomial hmem
  clear hmem
  obtain ⟨preimage, rfl⟩ := auxiliaryCoordinateEquiv.surjective polynomial
  let subalgebra := Algebra.adjoin ℂ ({auxiliaryU, auxiliaryV} : Set CoordinatePolynomial)
  induction preimage using MvPolynomial.induction_on with
  | C scalar =>
    have hconstant : auxiliaryCoordinateEquiv (MvPolynomial.C scalar) = MvPolynomial.C scalar :=
      auxiliaryCoordinateEquiv.commutes scalar
    rw [hconstant]
    exact subalgebra.algebraMap_mem scalar
  | add first second hfirst hsecond =>
    rw [map_add]
    exact subalgebra.add_mem hfirst hsecond
  | mul_X polynomial coordinate hpolynomial =>
    rw [map_mul]
    apply subalgebra.mul_mem hpolynomial
    fin_cases coordinate
    · change auxiliaryCoordinateEquiv (MvPolynomial.X 0) ∈ subalgebra
      rw [auxiliaryCoordinateEquiv_X_zero]
      exact Algebra.subset_adjoin (by simp)
    · change auxiliaryCoordinateEquiv (MvPolynomial.X 1) ∈ subalgebra
      rw [auxiliaryCoordinateEquiv_X_one]
      exact Algebra.subset_adjoin (by simp)

/-- The quotient image of u vanishes in power n+1. -/
theorem coinvariant_auxiliaryU_pow_eq_zero (n : ℕ) [NeZero n] :
    (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU) ^ (n + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact auxiliaryU_pow_mem_coinvariantIdeal n

/-- The quotient image of v vanishes in power n+1. -/
theorem coinvariant_auxiliaryV_pow_eq_zero (n : ℕ) [NeZero n] :
    (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV) ^ (n + 1) = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact auxiliaryV_pow_mem_coinvariantIdeal n

/-- The quotient auxiliary coordinates generate the official coinvariant algebra. -/
theorem coinvariant_auxiliary_adjoin_eq_top (n : ℕ) [NeZero n] :
    Algebra.adjoin ℂ
      ({Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU,
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV} : Set (CoinvariantAlgebra n)) = ⊤ := by
  have hequal := congrArg
    (fun subalgebra : Subalgebra ℂ CoordinatePolynomial =>
      subalgebra.map (Ideal.Quotient.mkₐ ℂ (coinvariantIdeal n))) auxiliaryCoordinate_adjoin_eq_top
  rw [AlgHom.map_adjoin, Algebra.map_top] at hequal
  simp only [Set.image_insert_eq, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk] at hequal
  exact hequal.trans ((AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective _ _))

/-- The official coinvariant algebra is finite-dimensional over the complex numbers. -/
theorem coinvariantAlgebra_finite (n : ℕ) [NeZero n] : Module.Finite ℂ (CoinvariantAlgebra n) := by
  have hintegral : ∀ element ∈
      ({Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU,
        Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV} : Set (CoinvariantAlgebra n)),
      IsIntegral ℂ element := by
    intro element helement
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at helement
    rcases helement with rfl | rfl
    · apply IsIntegral.of_pow (Nat.succ_pos n)
      rw [coinvariant_auxiliaryU_pow_eq_zero]
      exact isIntegral_zero
    · apply IsIntegral.of_pow (Nat.succ_pos n)
      rw [coinvariant_auxiliaryV_pow_eq_zero]
      exact isIntegral_zero
  have hfinite := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.toFinite _) hintegral
  rw [coinvariant_auxiliary_adjoin_eq_top] at hfinite
  have := hfinite
  exact Module.Finite.of_surjective (Subalgebra.topEquiv.toLinearMap)
    Subalgebra.topEquiv.surjective

end Schubert.Dihedral
