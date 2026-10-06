import Schubert.Splines.PolynomialModuleQuotientBasis

/-! # Spanning the polynomial augmentation quotient -/

noncomputable section
namespace Schubert.Splines

variable {K P M I J : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable [Module (MvPolynomial P K) M] [IsScalarTower K (MvPolynomial P K) M]
variable (basis : Module.Basis I (MvPolynomial P K) M)

include basis

/-- Polynomial scalar multiplication descends to its constant coefficient. -/
theorem polynomial_quotient_smul (polynomial : MvPolynomial P K) (value : M) :
    let quotient := (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K
    quotient.mkQ (polynomial • value) = polynomial.constantCoeff • quotient.mkQ value := by
  intro quotient
  apply (QuotientBasis.coordinates_bijective basis).1
  rw [map_smul (polynomialBasisQuotientCoordinates basis)]
  change polynomialBasisAugmentation basis (polynomial • value) =
    polynomial.constantCoeff • polynomialBasisAugmentation basis value
  ext index
  simp only [polynomialBasisAugmentation_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul, map_mul]

/-- Any polynomial-module generating family spans its augmentation quotient over coefficients. -/
theorem polynomial_quotient_span (values : J → M)
    (hspan : Submodule.span (MvPolynomial P K) (Set.range values) = ⊤) :
    let quotient := (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K
    Submodule.span K (Set.range fun index => quotient.mkQ (values index)) = ⊤ := by
  intro quotient
  rw [Submodule.eq_top_iff_forall_basis_mem (polynomialModuleQuotientBasis basis)]
  intro index
  rw [polynomialModuleQuotientBasis_apply]
  have hmem : basis index ∈ Submodule.span (MvPolynomial P K) (Set.range values) := by
    rw [hspan]
    exact Submodule.mem_top
  have hquotientMem : ∀ value, value ∈ Submodule.span (MvPolynomial P K) (Set.range values) →
      quotient.mkQ value ∈ Submodule.span K (Set.range fun other =>
        quotient.mkQ (values other)) := by
    intro value hvalue
    induction hvalue using Submodule.span_induction with
    | mem value hvalue =>
      obtain ⟨other, rfl⟩ := hvalue
      exact Submodule.subset_span (Set.mem_range_self other)
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add first second _ _ hfirst hsecond =>
      rw [map_add]
      exact Submodule.add_mem _ hfirst hsecond
    | smul polynomial value _ hvalue =>
      rw [polynomial_quotient_smul basis]
      exact Submodule.smul_mem _ _ hvalue
  exact hquotientMem (basis index) hmem

end Schubert.Splines
