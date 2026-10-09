import DihedralHessenberg.FiniteGroupCharacters.TensorPieceBasis
import Mathlib.LinearAlgebra.DirectSum.Basis
import DihedralHessenberg.FiniteGroupCharacters.DegreePairs
import TauCeti.RingTheory.MvPolynomial.Finrank

/-! # Ordinary homogeneous tensor components as degreewise direct sums -/

noncomputable section
open scoped TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- The arbitrary restricted homogeneous basis keeps its ambient vector. -/
theorem homogeneousFiberBasis_apply {K Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (index : {index : I // weights index = degree}) :
    (Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis degree index).val =
      basis index.val := by
  simp [Schubert.Splines.arbitraryHomogeneousPieceBasis]

/-- The ordinary tensor degree is the direct sum of its factor degree tensors. -/
def tensorDegreeEquiv {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    tensorPiece (P := P) pieces degree ≃ₗ[K]
      ⨁ split : Fin (degree + 1),
        (MvPolynomial.homogeneousSubmodule P K split.val) ⊗[K] pieces (degree - split.val) :=
  (tensorPieceBasis pieces basis weights hbasis degree).equiv
    (DFinsupp.basis fun split : Fin (degree + 1) =>
      (TauCeti.homogeneousMonomialBasis (R := K) split.val).tensorProduct
        (Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
          (degree - split.val)))
    (degreePairsEquiv weights degree)

/-- Joining one homogeneous tensor basis vector preserves its pure tensor. -/
theorem tensorDegreeEquiv_symm_basis {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (split : Fin (degree + 1)) (exponent : {exponent : P →₀ ℕ // exponent.degree = split.val})
    (index : {index : I // weights index = degree - split.val}) :
    ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of (fun split : Fin (degree + 1) =>
        MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)) split
        (TauCeti.homogeneousMonomialBasis (R := K) split.val exponent ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - split.val) index))).val =
      MvPolynomial.monomial exponent.val 1 ⊗ₜ[K] basis index.val := by
  classical
  let pair := (degreePairsEquiv weights degree).symm ⟨split, exponent, index⟩
  have hmap : tensorDegreeEquiv pieces basis weights hbasis degree
      (tensorPieceBasis pieces basis weights hbasis degree pair) =
      DirectSum.of (fun split : Fin (degree + 1) =>
        MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)) split
        (TauCeti.homogeneousMonomialBasis (R := K) split.val exponent ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - split.val) index) := by
    rw [tensorDegreeEquiv, Module.Basis.equiv_apply]
    change DFinsupp.basis _ ((degreePairsEquiv weights degree)
      ((degreePairsEquiv weights degree).symm ⟨split, exponent, index⟩)) = _
    rw [Equiv.apply_symm_apply]
    simp [DFinsupp.basis, Module.Basis.tensorProduct_apply]
    rfl
  rw [← hmap, LinearEquiv.symm_apply_apply, tensorPieceBasis_apply]
  rfl

/-- Joining a homogeneous component sends every pure tensor to its ambient tensor. -/
theorem tensorDegreeEquiv_symm_tmul {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (split : Fin (degree + 1)) (polynomial : MvPolynomial.homogeneousSubmodule P K split.val)
    (vector : pieces (degree - split.val)) :
    ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of (fun split : Fin (degree + 1) =>
        MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)) split
        (polynomial ⊗ₜ[K] vector))).val = polynomial.val ⊗ₜ[K] vector.val := by
  classical
  let family (split : Fin (degree + 1)) :=
    MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)
  have hmap : (tensorPiece (P := P) pieces degree).subtype.comp
      ((tensorDegreeEquiv pieces basis weights hbasis degree).symm.toLinearMap.comp
        (DirectSum.lof K (Fin (degree + 1)) family split)) =
      TensorProduct.map (MvPolynomial.homogeneousSubmodule P K split.val).subtype
        (pieces (degree - split.val)).subtype := by
    apply ((TauCeti.homogeneousMonomialBasis (R := K) split.val).tensorProduct
      (Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
        (degree - split.val))).ext
    intro pair
    rw [Module.Basis.tensorProduct_apply']
    change ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of family split
        (TauCeti.homogeneousMonomialBasis (R := K) split.val pair.1 ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - split.val) pair.2))).val = _
    rw [tensorDegreeEquiv_symm_basis, TensorProduct.map_tmul]
    simp only [Submodule.coe_subtype, TauCeti.coe_homogeneousMonomialBasis,
      homogeneousFiberBasis_apply]
  have hvalue := LinearMap.congr_fun hmap (polynomial ⊗ₜ[K] vector)
  change ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.of family split (polynomial ⊗ₜ[K] vector))).val =
      TensorProduct.map _ _ (polynomial ⊗ₜ[K] vector) at hvalue
  rw [TensorProduct.map_tmul] at hvalue
  exact hvalue

end Schubert.FiniteGroupCharacters
