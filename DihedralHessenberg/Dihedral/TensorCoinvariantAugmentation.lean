import DihedralHessenberg.Dihedral.InvariantTensorEvaluation
import DihedralHessenberg.Dihedral.CoinvariantSpanning

/-! Constant-coefficient evaluation is compatible with the invariant scalar action. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral

/-- Constant-coefficient evaluation is compatible with the invariant scalar action. -/
def constantCoinvariantHom (n : ℕ) [NeZero n] :
    CoordinatePolynomial →ₐ[invariantSubalgebra n] CoinvariantAlgebra n where
  __ := (algebraMap ℂ (CoinvariantAlgebra n)).comp MvPolynomial.constantCoeff
  commutes' scalar := by
    change Ideal.Quotient.mk (coinvariantIdeal n) (MvPolynomial.C scalar.val.constantCoeff) =
      Ideal.Quotient.mk (coinvariantIdeal n) scalar.val
    exact (coinvariant_mk_invariant_eq_constant n scalar.val scalar.property).symm

/-- The second tensor factor is augmented while the first retains its coinvariant class. -/
def tensorAugmentation (n : ℕ) [NeZero n] :
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial →ₐ[CoordinatePolynomial]
      CoinvariantAlgebra n :=
  AlgHom.liftEquiv (invariantSubalgebra n) CoordinatePolynomial CoordinatePolynomial
    (CoinvariantAlgebra n) (constantCoinvariantHom n)

/-- Augmentation of a pure tensor is its first class times the second constant coefficient. -/
theorem tensorAugmentation_tmul (n : ℕ) [NeZero n]
    (first second : CoordinatePolynomial) :
    tensorAugmentation n (first ⊗ₜ[invariantSubalgebra n] second) =
      Ideal.Quotient.mk (coinvariantIdeal n) first *
        algebraMap ℂ (CoinvariantAlgebra n) second.constantCoeff := by
  rw [tensorAugmentation, AlgHom.liftEquiv_tmul, Algebra.smul_def]
  rfl

end Schubert.Dihedral
