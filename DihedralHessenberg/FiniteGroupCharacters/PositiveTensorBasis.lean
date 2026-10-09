import DihedralHessenberg.FiniteGroupCharacters.PositiveTensorPiece
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Basis vectors in positive scalar tensor components -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- Positive scalar total-degree fibers form a basis of the degree intersection. -/
def positiveTensorPieceBasis {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    Module.Basis
      {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree ∧ pair.1 ≠ 0} K
      ↥(positiveTensor (K := K) (P := P) (Q := Q) ⊓ tensorPiece (P := P) pieces degree) :=
  (Module.Basis.span (((MvPolynomial.basisMonomials P K).tensorProduct basis).linearIndependent.comp
    Subtype.val Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (positive_tensor_piece pieces basis weights hbasis degree).symm)

/-- Each positive component basis vector is its pure monomial tensor. -/
theorem positiveTensorPieceBasis_apply {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (index : {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree ∧ pair.1 ≠ 0}) :
    (positiveTensorPieceBasis pieces basis weights hbasis degree index).val =
      MvPolynomial.monomial index.val.1 1 ⊗ₜ[K] basis index.val.2 := by
  simp [positiveTensorPieceBasis, Module.Basis.tensorProduct_apply']

end Schubert.FiniteGroupCharacters
