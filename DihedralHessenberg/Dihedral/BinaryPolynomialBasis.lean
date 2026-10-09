import DihedralHessenberg.Dihedral.PolynomialWeights

/-! # Finite auxiliary bases of the binary polynomial representations -/

noncomputable section
namespace Schubert.Dihedral

/-- The polynomial degree basis indexed by its first auxiliary exponent. -/
def binaryPolynomialBasis (degree : ℕ) :
    Module.Basis (Fin (degree + 1)) ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree) :=
  (auxiliaryPieceBasis degree).reindex (binaryExponentEquiv degree)

/-- The finite degree basis vector is its auxiliary monomial. -/
theorem binaryPolynomialBasis_product (degree : ℕ) (index : Fin (degree + 1)) :
    (binaryPolynomialBasis degree index).val =
      auxiliaryU ^ index.val * auxiliaryV ^ (degree - index.val) := by
  rw [binaryPolynomialBasis, Module.Basis.reindex_apply, auxiliaryPieceBasis_product,
    binaryExponentEquiv_first, binaryExponentEquiv_second]

/-- The first reflection reverses the degree basis with its total-degree sign. -/
theorem binaryPolynomialBasis_s1 (n : ℕ) [NeZero n] (degree : ℕ)
    (index : Fin (degree + 1)) :
    polynomialPieceRepresentation n degree (firstSimpleReflection n)
        (binaryPolynomialBasis degree index) =
      (-1 : ℂ) ^ degree • binaryPolynomialBasis degree index.rev := by
  apply Subtype.ext
  change polynomialAction n (firstSimpleReflection n) (binaryPolynomialBasis degree index).val =
    (-1 : ℂ) ^ degree • (binaryPolynomialBasis degree index.rev).val
  rw [binaryPolynomialBasis_product, binaryPolynomialBasis_product]
  have hbound := index.isLt
  have hrev : index.rev.val = degree - index.val := by simp [Fin.val_rev]
  have hsub : degree - (degree - index.val) = index.val := by omega
  rw [hrev, hsub, map_mul, map_pow, map_pow,
    polynomialAction_firstSimple_auxiliaryU, polynomialAction_firstSimple_auxiliaryV]
  rw [neg_eq_neg_one_mul auxiliaryV, neg_eq_neg_one_mul auxiliaryU, mul_pow, mul_pow]
  simp only [Algebra.smul_def]
  change _ = MvPolynomial.C _ * _
  have hsum : index.val + (degree - index.val) = degree := by omega
  have hphase : (MvPolynomial.C ((-1 : ℂ) ^ degree) : CoordinatePolynomial) =
      (-1) ^ index.val * (-1) ^ (degree - index.val) := by
    rw [map_pow, map_neg, map_one, ← pow_add, hsum]
  rw [hphase]
  ring

/-- Rotation acts on the finite degree basis with its integer cyclic weight. -/
theorem binaryPolynomialBasis_r (n : ℕ) [NeZero n] (degree : ℕ)
    (coordinate : ZMod n) (index : Fin (degree + 1)) :
    polynomialPieceRepresentation n degree (.r coordinate) (binaryPolynomialBasis degree index) =
      ZMod.stdAddChar ((((degree : ℤ) - 2 * index.val : ℤ) : ZMod n) * coordinate) •
        binaryPolynomialBasis degree index := by
  apply Subtype.ext
  change polynomialAction n (.r coordinate) (binaryPolynomialBasis degree index).val =
    _ • (binaryPolynomialBasis degree index).val
  rw [binaryPolynomialBasis_product, map_mul, map_pow, map_pow,
    polynomialAction_r_auxiliaryU, polynomialAction_r_auxiliaryV]
  simp only [mul_pow, Algebra.smul_def]
  change _ = MvPolynomial.C _ * _
  rw [← map_pow, ← map_pow]
  have hbound := index.isLt
  have hweight : ((degree - index.val : ℕ) : ZMod n) - (index.val : ZMod n) =
      (((degree : ℤ) - 2 * index.val : ℤ) : ZMod n) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hweight, ← rotation_monomial_additive]
  rw [map_mul]
  ring

end Schubert.Dihedral
