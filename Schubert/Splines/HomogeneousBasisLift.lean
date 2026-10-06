import Schubert.Splines.WeightedBasis
import Schubert.Splines.PolynomialBasisCoordinates
import Schubert.Splines.PolynomialModuleQuotientBasis

/-! # Homogeneous lifting of finite polynomial bases -/

noncomputable section

namespace Schubert.Splines

/-- Homogeneous lifts with the same coefficient augmentation form a polynomial basis. -/
theorem homogeneous_basis_lift {K P M I : Type*} [CommRing K] [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module K M] [Module (MvPolynomial P K) M]
    [IsScalarTower K (MvPolynomial P K) M]
    (pieces : ℕ → Submodule K M) [DirectSum.Decomposition pieces]
    (basis : Module.Basis I (MvPolynomial P K) M) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : M),
      polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
        polynomial • value ∈ pieces (scalarDegree + valueDegree))
    (transform : M →ₗ[MvPolynomial P K] M)
    (hhomogeneous : ∀ index, transform (basis index) ∈ pieces (weights index))
    (haugmentation : ∀ first second,
      (basis.repr (transform (basis second)) first).constantCoeff =
        if first = second then 1 else 0)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    ∃ lifted : Module.Basis I (MvPolynomial P K) M,
      ∀ index, lifted index = transform (basis index) := by
  apply weighted_basis_lift basis weights transform _ bound hbound
  intro first second hweight
  rw [polynomial_basis_repr_constant pieces basis weights hbasis hsmul (weights second)
    (hhomogeneous second) first hweight, haugmentation first second]
  by_cases heq : first = second <;> simp [heq]

/-- Homogeneous representatives of a descended basis lift to a polynomial module basis. -/
theorem homogeneous_quotient_basis_lift {K P M I : Type*} [CommRing K]
    [Fintype I] [DecidableEq I] [AddCommGroup M] [Module K M]
    [Module (MvPolynomial P K) M] [IsScalarTower K (MvPolynomial P K) M]
    (pieces : ℕ → Submodule K M) [DirectSum.Decomposition pieces]
    (basis : Module.Basis I (MvPolynomial P K) M) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : M),
      polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
        polynomial • value ∈ pieces (scalarDegree + valueDegree))
    (values : I → M) (hhomogeneous : ∀ index, values index ∈ pieces (weights index))
    (hquotient : ∀ index,
      Submodule.Quotient.mk (p := (MvPolynomial.idealOfVars P K •
        (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K) (values index) =
      Submodule.Quotient.mk (basis index))
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    ∃ lifted : Module.Basis I (MvPolynomial P K) M, ∀ index, lifted index = values index := by
  let transform := basis.constr (MvPolynomial P K) values
  have htransform : ∀ index, transform (basis index) = values index :=
    basis.constr_basis _ values
  have haug : ∀ first second,
      (basis.repr (transform (basis second)) first).constantCoeff =
        if first = second then 1 else 0 := by
    intro first second
    have hcoords := congrArg (polynomialBasisQuotientCoordinates basis) (hquotient second)
    rw [polynomialBasisQuotientCoordinates_mk, polynomialBasisQuotientCoordinates_mk] at hcoords
    have hentry := congrArg (fun coordinates => coordinates first) hcoords
    rw [polynomialBasisAugmentation_apply, polynomialBasisAugmentation_apply] at hentry
    rw [htransform]
    rw [hentry]
    by_cases heq : first = second <;> simp [Module.Basis.repr_self, heq]
  obtain ⟨lifted, hlifted⟩ := homogeneous_basis_lift pieces basis weights hbasis hsmul transform
    (fun index => htransform index ▸ hhomogeneous index) haug bound hbound
  exact ⟨lifted, fun index => (hlifted index).trans (htransform index)⟩

end Schubert.Splines
