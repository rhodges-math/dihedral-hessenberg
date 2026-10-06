import Schubert.Splines.PolynomialAugmentation
import Schubert.Splines.BasisIdealCoordinates
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Algebra.Algebra.Tower

/-! # Constant-coefficient coordinates of polynomial-basis modules

This coordinate map is onto; its kernel is the variable ideal times the module.
It is the algebraic input for descending a polynomial basis to coefficient scalars.
-/

noncomputable section

namespace Schubert.Splines

variable {K P M I : Type*} [CommRing K] [AddCommGroup M]
variable [Module K M] [Module (MvPolynomial P K) M]
variable [IsScalarTower K (MvPolynomial P K) M]

/-- Apply constant coefficients to every coordinate in a polynomial basis. -/
def polynomialBasisAugmentation (basis : Module.Basis I (MvPolynomial P K) M) :
    M →ₗ[K] (I →₀ K) :=
  (Finsupp.mapRange.linearMap (MvPolynomial.lcoeff K 0)).comp
    (basis.repr.toLinearMap.restrictScalars K)

/-- Augmentation coordinates are the constant coefficients of basis coordinates. -/
theorem polynomialBasisAugmentation_apply
    (basis : Module.Basis I (MvPolynomial P K) M) (value : M) (index : I) :
    polynomialBasisAugmentation basis value index =
      MvPolynomial.constantCoeff (basis.repr value index) := rfl

/-- Augmentation vanishes exactly on variable-ideal multiples of the whole module. -/
theorem polynomialBasisAugmentation_eq_zero_iff
    (basis : Module.Basis I (MvPolynomial P K) M) (value : M) :
    polynomialBasisAugmentation basis value = 0 ↔
      value ∈ MvPolynomial.idealOfVars P K • (⊤ : Submodule (MvPolynomial P K) M) := by
  rw [mem_ideal_smul_top_iff_basis_coordinates basis]
  simp only [Finsupp.ext_iff, polynomialBasisAugmentation_apply, Finsupp.zero_apply,
    _root_.Schubert.Splines.PolynomialAugmentation.mem_iff_constantCoeff_zero]

/-- Every finite coefficient vector is the augmentation of a polynomial-basis vector. -/
theorem polynomialBasisAugmentation_surjective
    (basis : Module.Basis I (MvPolynomial P K) M) :
    Function.Surjective (polynomialBasisAugmentation basis) := by
  intro coefficients
  refine ⟨basis.repr.symm (coefficients.mapRange MvPolynomial.C (by simp)), ?_⟩
  ext index
  simp [polynomialBasisAugmentation_apply]

end Schubert.Splines
