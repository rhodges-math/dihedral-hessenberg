import Schubert.Dihedral.FractionTensor
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.BaseChange

/-! # Localization of the polynomial algebra by invariant denominators -/

noncomputable section
open scoped TensorProduct nonZeroDivisors
namespace Schubert.Dihedral

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Invariant denominators already localize the polynomial algebra to its entire fraction field. -/
theorem fraction_localization (n : ℕ) [NeZero n] :
    IsLocalization (Algebra.algebraMapSubmonoid CoordinatePolynomial
      (nonZeroDivisors (invariantSubalgebra n))) (FractionRing CoordinatePolynomial) := by
  let := polynomialMulAction n
  have hgroup := polynomial_isGaloisGroup n
  have : Algebra.IsIntegral (invariantSubalgebra n) CoordinatePolynomial :=
    hgroup.isInvariant.isIntegral
  have : IsGalois (FractionRing (invariantSubalgebra n))
      (FractionRing CoordinatePolynomial) := fraction_isGalois n
  have : IsIntegralClosure CoordinatePolynomial (invariantSubalgebra n)
      (FractionRing CoordinatePolynomial) := inferInstance
  exact IsIntegralClosure.isLocalization (invariantSubalgebra n)
    (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial)
    CoordinatePolynomial

/-- Tensoring the polynomial algebra with invariant fractions gives its fraction field. -/
def invariantFractionEquiv (n : ℕ) [NeZero n] :
    FractionRing (invariantSubalgebra n) ⊗[invariantSubalgebra n] CoordinatePolynomial
      ≃ₐ[FractionRing (invariantSubalgebra n)] FractionRing CoordinatePolynomial := by
  have := fraction_localization n
  have hpush : Algebra.IsPushout (invariantSubalgebra n) CoordinatePolynomial
      (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial) :=
    (Algebra.isLocalization_iff_isPushout
      (nonZeroDivisors (invariantSubalgebra n)) (FractionRing (invariantSubalgebra n))).mp
      (fraction_localization n)
  have := hpush.symm
  exact Algebra.IsPushout.equiv (invariantSubalgebra n)
    (FractionRing (invariantSubalgebra n)) CoordinatePolynomial
    (FractionRing CoordinatePolynomial)

/-- The invariant localization retains the product of the embedded tensor factors. -/
theorem invariantFractionEquiv_tmul (n : ℕ) [NeZero n]
    (fraction : FractionRing (invariantSubalgebra n)) (polynomial : CoordinatePolynomial) :
    invariantFractionEquiv n (fraction ⊗ₜ[invariantSubalgebra n] polynomial) =
      algebraMap (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial)
        fraction * algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial)
        polynomial := by
  simp [invariantFractionEquiv, Algebra.IsPushout.equiv_tmul]

/-- The first-fraction polynomial tensor has the canonical Galois-product splitting. -/
def fractionPolynomialEquiv (n : ℕ) [NeZero n] :
    FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial
      ≃ₐ[FractionRing CoordinatePolynomial]
      (DihedralGroup n → FractionRing CoordinatePolynomial) :=
  (Algebra.TensorProduct.cancelBaseChange (invariantSubalgebra n)
    (FractionRing (invariantSubalgebra n)) (FractionRing CoordinatePolynomial)
    (FractionRing CoordinatePolynomial) CoordinatePolynomial).symm.trans
      ((Algebra.TensorProduct.congr
        (AlgEquiv.refl : FractionRing CoordinatePolynomial ≃ₐ[FractionRing CoordinatePolynomial]
          FractionRing CoordinatePolynomial) (invariantFractionEquiv n)).trans
        (fractionTensorEquiv n))

/-- The localized polynomial tensor splitting retains the product formula. -/
theorem fractionPolynomialEquiv_tmul (n : ℕ) [NeZero n]
    (fraction : FractionRing CoordinatePolynomial) (polynomial : CoordinatePolynomial)
    (element : DihedralGroup n) :
    fractionPolynomialEquiv n (fraction ⊗ₜ[invariantSubalgebra n] polynomial) element =
      fraction * algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial)
        (polynomialAction n element polynomial) := by
  simp only [fractionPolynomialEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
    invariantFractionEquiv_tmul,
    map_one, one_mul, fractionTensorEquiv_tmul, fractionMulAction_map]

end Schubert.Dihedral
