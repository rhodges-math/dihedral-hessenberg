import Schubert.Dihedral.AugmentationQuotientBasis
import Schubert.Dihedral.InvariantFreeness

/-! # The explicit dihedral coinvariant basis

The invariant-module axial basis descends through invariant augmentation to the
coinvariant algebra. The quotient has dimension exactly 2n.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Extending the invariant augmentation kernel gives the official coinvariant ideal. -/
theorem _root_.Schubert.Dihedral.Coinvariant.ideal_eq_map_augmentation_kernel (n : ℕ) [NeZero n]
    (augmentation : invariantSubalgebra n →ₐ[ℂ] ℂ)
    (haugmentation : ∀ scalar, augmentation scalar =
      MvPolynomial.constantCoeff (scalar : CoordinatePolynomial)) :
    Ideal.map (algebraMap (invariantSubalgebra n) CoordinatePolynomial)
      (RingHom.ker augmentation) = coinvariantIdeal n := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro scalar hscalar
    change (scalar : CoordinatePolynomial) ∈ coinvariantIdeal n
    apply positiveInvariant_mem_coinvariantIdeal n _ scalar.property
    simpa only [RingHom.mem_ker, haugmentation] using hscalar
  · apply Ideal.span_le.mpr
    intro polynomial hpolynomial
    obtain ⟨hinvariant, hzero⟩ := hpolynomial
    have hscalar : (⟨polynomial, hinvariant⟩ : invariantSubalgebra n) ∈
        RingHom.ker augmentation := by
      simp only [RingHom.mem_ker, haugmentation]
      exact hzero
    exact Ideal.mem_map_of_mem (algebraMap (invariantSubalgebra n) CoordinatePolynomial) hscalar

/-- There is a coinvariant basis consisting of the axial rotation-block classes. -/
theorem exists_coinvariant_axial_basis (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    ∃ basis : Module.Basis (Fin n × Fin 2) ℂ (CoinvariantAlgebra n),
      ∀ index, basis index = Ideal.Quotient.mk (coinvariantIdeal n)
        ((if index.1.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
          else ![auxiliaryU ^ (n - index.1.val), auxiliaryV ^ index.1.val]) index.2) := by
  let augmentation : invariantSubalgebra n →ₐ[ℂ] ℂ :=
    { toFun := fun scalar => MvPolynomial.constantCoeff (scalar : CoordinatePolynomial)
      map_zero' := by simp
      map_one' := by simp
      map_add' := by intros; simp
      map_mul' := by intros; simp
      commutes' := by intro scalar; simp }
  have hideal := _root_.Schubert.Dihedral.Coinvariant.ideal_eq_map_augmentation_kernel n
    augmentation (fun _ => rfl)
  obtain ⟨basis, hbasis⟩ := exists_invariant_axial_basis n hthree
  obtain ⟨quotientBasis, hquotient⟩ := exists_augmentation_quotient_basis augmentation basis
  let quotientEquiv := (Ideal.quotientEquivAlgOfEq ℂ hideal).toLinearEquiv
  refine ⟨quotientBasis.map quotientEquiv, fun index => ?_⟩
  rw [Module.Basis.map_apply, hquotient, hbasis]
  exact Ideal.quotientEquivAlgOfEq_mk ℂ hideal _

/-- The coinvariant algebra has dimension exactly the dihedral order 2n. -/
theorem coinvariantAlgebra_finrank (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Module.finrank ℂ (CoinvariantAlgebra n) = 2 * n := by
  obtain ⟨basis, _⟩ := exists_coinvariant_axial_basis n hthree
  rw [Module.finrank_eq_card_basis basis, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  omega

end Schubert.Dihedral
