import DihedralHessenberg.Splines.PolynomialBasisAugmentation
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Descending polynomial bases through the variable ideal

The coefficient-coordinate map identifies the variable-ideal module quotient
with finitely supported coefficient vectors, for arbitrary basis index types.
-/

noncomputable section

namespace Schubert.Splines

variable {K P M I : Type*} [CommRing K] [AddCommGroup M]
variable [Module K M] [Module (MvPolynomial P K) M]
variable [IsScalarTower K (MvPolynomial P K) M]

/-- Constant-coefficient basis coordinates descend to the variable-ideal quotient. -/
def polynomialBasisQuotientCoordinates (basis : Module.Basis I (MvPolynomial P K) M) :
    (M ⧸ (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K) →ₗ[K] (I →₀ K) :=
  Submodule.liftQ _ (polynomialBasisAugmentation basis) (by
    intro value hvalue
    exact (polynomialBasisAugmentation_eq_zero_iff basis value).2 hvalue)

/-- Quotient coordinates recover the augmentation of a representative. -/
theorem polynomialBasisQuotientCoordinates_mk
    (basis : Module.Basis I (MvPolynomial P K) M) (value : M) :
    polynomialBasisQuotientCoordinates basis (Submodule.Quotient.mk value) =
      polynomialBasisAugmentation basis value := rfl

/-- Descended constant-coefficient basis coordinates are bijective. -/
theorem _root_.Schubert.Splines.QuotientBasis.coordinates_bijective
    (basis : Module.Basis I (MvPolynomial P K) M) :
    Function.Bijective (polynomialBasisQuotientCoordinates basis) := by
  let piece := (MvPolynomial.idealOfVars P K •
    (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K
  constructor
  · apply (injective_iff_map_eq_zero (polynomialBasisQuotientCoordinates basis)).2
    intro value hzero
    obtain ⟨representative, rfl⟩ := piece.mkQ_surjective value
    change polynomialBasisAugmentation basis representative = 0 at hzero
    exact (Submodule.Quotient.mk_eq_zero piece).mpr
      ((polynomialBasisAugmentation_eq_zero_iff basis representative).1 hzero)
  · intro coefficients
    obtain ⟨representative, hrepresentative⟩ :=
      polynomialBasisAugmentation_surjective basis coefficients
    exact ⟨Submodule.Quotient.mk representative, hrepresentative⟩

/-- A polynomial basis descends to a coefficient-ring basis of the variable-ideal quotient. -/
def polynomialModuleQuotientBasis (basis : Module.Basis I (MvPolynomial P K) M) :
    Module.Basis I K (M ⧸ (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K) :=
  ⟨LinearEquiv.ofBijective (polynomialBasisQuotientCoordinates basis)
    (_root_.Schubert.Splines.QuotientBasis.coordinates_bijective basis)⟩

/-- The descended basis vector is the quotient class of its polynomial basis vector. -/
theorem polynomialModuleQuotientBasis_apply
    (basis : Module.Basis I (MvPolynomial P K) M) (index : I) :
    polynomialModuleQuotientBasis basis index = Submodule.Quotient.mk (basis index) := by
  classical
  rw [Module.Basis.apply_eq_iff]
  ext coordinate
  by_cases hindex : index = coordinate <;>
    simp [polynomialModuleQuotientBasis, polynomialBasisQuotientCoordinates_mk,
      polynomialBasisAugmentation_apply, hindex]

/-- The coefficient rank of a variable-ideal quotient equals its polynomial basis cardinality. -/
theorem polynomialModuleQuotientBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I (MvPolynomial P K) M) :
    Module.finrank K (M ⧸ (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K) = Nat.card I :=
  Module.finrank_eq_nat_card_basis (polynomialModuleQuotientBasis basis)
end Schubert.Splines
