import Schubert.Dihedral.FirstLocalization

/-! # The fixed-field Galois tensor splitting -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral

attribute [local instance] FractionRing.liftAlgebra

/-- The embedded invariant fraction field equals the fixed subfield. -/
theorem fraction_fixed_subfield (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    (algebraMap (FractionRing (invariantSubalgebra n))
      (FractionRing CoordinatePolynomial)).fieldRange =
      FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  ext value
  exact Set.ext_iff.mp (fraction_fixed n) value

/-- The group is Galois over its fixed subfield. -/
theorem fraction_fixed_galois (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    IsGaloisGroup (DihedralGroup n)
      (FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial))
      (FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  have hgroup := fraction_isGaloisGroup n
  refine ⟨hgroup.faithful, inferInstance, ?_⟩
  exact ⟨fun value hfixed => ⟨⟨value, hfixed⟩, rfl⟩⟩

/-- The extension over the fixed subfield is Galois. -/
theorem fraction_fixed_isGalois (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    IsGalois (FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial))
      (FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  have := fraction_fixed_galois n
  exact IsGaloisGroup.isGalois (DihedralGroup n)
    (FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial))
    (FractionRing CoordinatePolynomial)

/-- The canonical tensor splitting uses the fixed subfield as its balancing ring. -/
def fixedTensorEquiv (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    FractionRing CoordinatePolynomial ⊗[
      FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial)]
      FractionRing CoordinatePolynomial ≃ₐ[FractionRing CoordinatePolynomial]
      (DihedralGroup n → FractionRing CoordinatePolynomial) := by
  let := fractionMulAction n
  have := fraction_fixed_galois n
  exact Splines.galoisTensorEquiv (DihedralGroup n)
    (FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial))
    (FractionRing CoordinatePolynomial)

/-- The fixed-field tensor splitting retains the exact action-product formula. -/
theorem fixedTensorEquiv_tmul (n : ℕ) [NeZero n]
    (first second : FractionRing CoordinatePolynomial) (element : DihedralGroup n) :
    letI := fractionMulAction n
    fixedTensorEquiv n (first ⊗ₜ[
      FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial)] second) element =
      first * element • second := rfl

/-- The first-localized polynomial tensor is the tensor square over the fixed subfield. -/
def polynomialFixedEquiv (n : ℕ) [NeZero n] :
    letI := fractionMulAction n
    FractionRing CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial
      ≃ₐ[FractionRing CoordinatePolynomial]
      FractionRing CoordinatePolynomial ⊗[
        FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial)]
        FractionRing CoordinatePolynomial :=
  (fractionPolynomialEquiv n).trans (fixedTensorEquiv n).symm

/-- The fixed-field identification embeds the polynomial second factor without altering tensors. -/
theorem polynomialFixedEquiv_tmul (n : ℕ) [NeZero n]
    (fraction : FractionRing CoordinatePolynomial) (polynomial : CoordinatePolynomial) :
    letI := fractionMulAction n
    polynomialFixedEquiv n (fraction ⊗ₜ[invariantSubalgebra n] polynomial) =
      fraction ⊗ₜ[
        FixedPoints.subfield (DihedralGroup n) (FractionRing CoordinatePolynomial)]
        algebraMap CoordinatePolynomial (FractionRing CoordinatePolynomial) polynomial := by
  let := fractionMulAction n
  apply (fixedTensorEquiv n).injective
  ext element
  simp only [polynomialFixedEquiv, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    fixedTensorEquiv_tmul, fractionPolynomialEquiv_tmul, fractionMulAction_map]

end Schubert.Dihedral
