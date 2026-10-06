import Schubert.Dihedral.FractionLocalization
import Mathlib.Algebra.Group.Pi.Units

/-! # The two-factor localization of the polynomial tensor -/

noncomputable section
open scoped TensorProduct nonZeroDivisors
namespace Schubert.Dihedral

/-- The first-fraction tensor localizes the polynomial tensor's first factor. -/
theorem first_tensor_localization (n : ℕ) [NeZero n] :
    let : Algebra (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
        (FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :=
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom (invariantSubalgebra n) CoordinatePolynomial
          (FractionRing CoordinatePolynomial)) (AlgHom.id (invariantSubalgebra n)
          CoordinatePolynomial)).toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid
        (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
        (nonZeroDivisors CoordinatePolynomial))
      (FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) := by
  let : Algebra (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
      (FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :=
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom (invariantSubalgebra n) CoordinatePolynomial
        (FractionRing CoordinatePolynomial)) (AlgHom.id (invariantSubalgebra n)
        CoordinatePolynomial)).toAlgebra
  let : Algebra CoordinatePolynomial
      (FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :=
    Algebra.TensorProduct.leftAlgebra
  have : IsScalarTower CoordinatePolynomial
      (CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
      (FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :=
    IsScalarTower.of_algebraMap_eq' (R := CoordinatePolynomial)
      (S := CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
      (A := FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial)
      (by
        apply RingHom.ext
        intro polynomial
        change algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial)
          polynomial ⊗ₜ[invariantSubalgebra n] 1 =
            (Algebra.TensorProduct.map
              (IsScalarTower.toAlgHom (invariantSubalgebra n) CoordinatePolynomial
                (FractionRing CoordinatePolynomial))
              (AlgHom.id (invariantSubalgebra n) CoordinatePolynomial))
              (polynomial ⊗ₜ[invariantSubalgebra n] 1)
        rw [Algebra.TensorProduct.map_tmul]
        rfl)
  exact IsLocalization.tensorProduct_tensorProduct (invariantSubalgebra n)
    CoordinatePolynomial (nonZeroDivisors CoordinatePolynomial)
    (FractionRing CoordinatePolynomial) (by
      apply RingHom.ext
      intro polynomial
      change (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom (invariantSubalgebra n) CoordinatePolynomial
          (FractionRing CoordinatePolynomial))
        (AlgHom.id (invariantSubalgebra n) CoordinatePolynomial))
        (1 ⊗ₜ[invariantSubalgebra n] polynomial) = 1 ⊗ₜ[invariantSubalgebra n] polynomial
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)

/-- Nonzero second-factor polynomials become units after localizing the first factor. -/
theorem second_tensor_unit (n : ℕ) [NeZero n] (polynomial : CoordinatePolynomial)
    (hnonzero : polynomial ≠ 0) :
    IsUnit (1 ⊗ₜ[invariantSubalgebra n] polynomial :
      FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) := by
  have hunit : IsUnit (fractionPolynomialEquiv n
      (1 ⊗ₜ[invariantSubalgebra n] polynomial)) := by
    apply Pi.isUnit_iff.mpr
    intro element
    rw [fractionPolynomialEquiv_tmul, one_mul]
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hnonzero
    apply (polynomialAction n element).injective
    exact (IsFractionRing.injective CoordinatePolynomial (FractionRing CoordinatePolynomial)
      (hzero.trans (map_zero _).symm)).trans (map_zero _).symm
  have hmap := hunit.map (fractionPolynomialEquiv n).symm.toMonoidHom
  change IsUnit ((fractionPolynomialEquiv n).symm
    (fractionPolynomialEquiv n (1 ⊗ₜ[invariantSubalgebra n] polynomial))) at hmap
  simpa only [AlgEquiv.symm_apply_apply] using hmap

end Schubert.Dihedral
