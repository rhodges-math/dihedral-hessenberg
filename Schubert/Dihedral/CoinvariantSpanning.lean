import Mathlib.LinearAlgebra.Dimension.Constructions
import Schubert.Dihedral.InvariantSpanning

/-! # Explicit spanning of the coinvariant algebra

Invariant coefficients become constant scalars in the coinvariant quotient.
The initial 2n axial powers therefore span the quotient over the complex numbers.
-/

noncomputable section

namespace Schubert.Dihedral

/-- An invariant and its constant coefficient have the same coinvariant class. -/
theorem coinvariant_mk_invariant_eq_constant (n : ℕ) [NeZero n]
    (polynomial : CoordinatePolynomial) (hinvariant : polynomial ∈ invariantSubalgebra n) :
    Ideal.Quotient.mk (coinvariantIdeal n) polynomial =
      Ideal.Quotient.mk (coinvariantIdeal n) (MvPolynomial.C polynomial.constantCoeff) := by
  apply Ideal.Quotient.eq.mpr
  apply positiveInvariant_mem_coinvariantIdeal
  · exact (invariantSubalgebra n).sub_mem hinvariant
      ((invariantSubalgebra n).algebraMap_mem _)
  · simp

/-- The initial 2n axial powers span the coinvariant algebra over the complex numbers. -/
theorem coinvariant_auxiliary_powers_span_eq_top (n : ℕ) [NeZero n] :
    Submodule.span ℂ
      (Set.range (fun index : Fin (n + 1) ⊕ Fin (n - 1) =>
        Ideal.Quotient.mkₐ ℂ (coinvariantIdeal n)
          (Sum.elim (fun first : Fin (n + 1) => auxiliaryU ^ first.val)
            (fun second : Fin (n - 1) => auxiliaryV ^ (second.val + 1)) index))) = ⊤ := by
  classical
  let family := Sum.elim (fun index : Fin (n + 1) => auxiliaryU ^ index.val)
    (fun index : Fin (n - 1) => auxiliaryV ^ (index.val + 1))
  let quotient := Ideal.Quotient.mkₐ ℂ (coinvariantIdeal n)
  let submodule := Submodule.span ℂ (Set.range (fun index => quotient (family index)))
  apply top_unique
  intro element htop
  clear htop
  obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective element
  have hspan : polynomial ∈ Submodule.span (invariantSubalgebra n) (Set.range family) := by
    rw [invariant_auxiliary_powers_span_eq_top]
    trivial
  change quotient polynomial ∈ submodule
  induction hspan using Submodule.span_induction with
  | mem polynomial hpolynomial =>
    obtain ⟨index, rfl⟩ := hpolynomial
    exact Submodule.subset_span ⟨index, rfl⟩
  | zero => simpa only [map_zero] using submodule.zero_mem
  | add first second _ _ hfirst hsecond =>
    simpa only [map_add] using submodule.add_mem hfirst hsecond
  | smul scalar polynomial _ hpolynomial =>
    change quotient ((scalar : CoordinatePolynomial) * polynomial) ∈ submodule
    rw [map_mul, show quotient (scalar : CoordinatePolynomial) =
      quotient (MvPolynomial.C (scalar : CoordinatePolynomial).constantCoeff) from
        coinvariant_mk_invariant_eq_constant n _ scalar.property]
    have hconstant := quotient.commutes (scalar : CoordinatePolynomial).constantCoeff
    change quotient (MvPolynomial.C (scalar : CoordinatePolynomial).constantCoeff) =
      algebraMap ℂ (CoinvariantAlgebra n) (scalar : CoordinatePolynomial).constantCoeff
      at hconstant
    rw [hconstant, ← Algebra.smul_def]
    exact submodule.smul_mem _ hpolynomial

/-- The coinvariant algebra has dimension at most the order 2n of the dihedral group. -/
theorem coinvariantAlgebra_finrank_le (n : ℕ) [NeZero n] :
    Module.finrank ℂ (CoinvariantAlgebra n) ≤ 2 * n := by
  have hbound : Module.finrank ℂ (CoinvariantAlgebra n) ≤
      Fintype.card (Fin (n + 1) ⊕ Fin (n - 1)) :=
    finrank_le_of_span_eq_top (coinvariant_auxiliary_powers_span_eq_top n)
  simp only [Fintype.card_sum, Fintype.card_fin] at hbound
  have hpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  omega

end Schubert.Dihedral
