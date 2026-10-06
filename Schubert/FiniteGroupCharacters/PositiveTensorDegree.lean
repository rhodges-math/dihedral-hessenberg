import Schubert.FiniteGroupCharacters.PositiveTensorBasis
import Schubert.FiniteGroupCharacters.TensorDegreeEquiv
import Schubert.FiniteGroupCharacters.PositiveDegreePairs

/-! # Splitting positive scalar tensor degrees -/

noncomputable section
open scoped TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- The positive scalar part of an ordinary tensor degree splits into its factor degree tensors. -/
def positiveTensorDegreeEquiv {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) ≃ₗ[K]
      ⨁ split : Fin degree,
        (MvPolynomial.homogeneousSubmodule P K (split.val + 1)) ⊗[K]
          pieces (degree - (split.val + 1)) :=
  (positiveTensorPieceBasis pieces basis weights hbasis degree).equiv
    (DFinsupp.basis fun split : Fin degree =>
      (TauCeti.homogeneousMonomialBasis (R := K) (split.val + 1)).tensorProduct
        (Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
          (degree - (split.val + 1))))
    (positiveDegreePairsEquiv weights degree)

/-- Joining one homogeneous tensor basis vector preserves its pure tensor. -/
theorem positiveTensorDegreeEquiv_symm_basis {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (split : Fin degree) (exponent : {exponent : P →₀ ℕ // exponent.degree = (split.val + 1)})
    (index : {index : I // weights index = degree - (split.val + 1)}) :
    ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of (fun split : Fin degree =>
        MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K]
          pieces (degree - (split.val + 1))) split
        (TauCeti.homogeneousMonomialBasis (R := K) (split.val + 1) exponent ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - (split.val + 1)) index))).val =
      MvPolynomial.monomial exponent.val 1 ⊗ₜ[K] basis index.val := by
  classical
  let pair := (positiveDegreePairsEquiv weights degree).symm ⟨split, exponent, index⟩
  have hmap : positiveTensorDegreeEquiv pieces basis weights hbasis degree
      (positiveTensorPieceBasis pieces basis weights hbasis degree pair) =
      DirectSum.of (fun split : Fin degree =>
        MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K]
          pieces (degree - (split.val + 1))) split
        (TauCeti.homogeneousMonomialBasis (R := K) (split.val + 1) exponent ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - (split.val + 1)) index) := by
    rw [positiveTensorDegreeEquiv, Module.Basis.equiv_apply]
    change DFinsupp.basis _ ((positiveDegreePairsEquiv weights degree)
      ((positiveDegreePairsEquiv weights degree).symm ⟨split, exponent, index⟩)) = _
    rw [Equiv.apply_symm_apply]
    simp [DFinsupp.basis, Module.Basis.tensorProduct_apply]
    rfl
  rw [← hmap, LinearEquiv.symm_apply_apply, positiveTensorPieceBasis_apply]
  rfl

/-- Joining a homogeneous component sends every pure tensor to its ambient tensor. -/
theorem positiveTensorDegreeEquiv_symm_tmul {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (split : Fin degree) (polynomial : MvPolynomial.homogeneousSubmodule P K (split.val + 1))
    (vector : pieces (degree - (split.val + 1))) :
    ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of (fun split : Fin degree =>
        MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K]
          pieces (degree - (split.val + 1))) split
        (polynomial ⊗ₜ[K] vector))).val = polynomial.val ⊗ₜ[K] vector.val := by
  classical
  let family (split : Fin degree) :=
    MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K] pieces (degree - (split.val + 1))
  have hmap : ((positiveTensor (P := P) ⊓ tensorPiece pieces degree)).subtype.comp
      ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm.toLinearMap.comp
        (DirectSum.lof K (Fin degree) family split)) =
      TensorProduct.map (MvPolynomial.homogeneousSubmodule P K (split.val + 1)).subtype
        (pieces (degree - (split.val + 1))).subtype := by
    apply ((TauCeti.homogeneousMonomialBasis (R := K) (split.val + 1)).tensorProduct
      (Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
        (degree - (split.val + 1)))).ext
    intro pair
    rw [Module.Basis.tensorProduct_apply']
    change ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
      (DirectSum.of family split
        (TauCeti.homogeneousMonomialBasis (R := K) (split.val + 1) pair.1 ⊗ₜ[K]
          Schubert.Splines.arbitraryHomogeneousPieceBasis pieces basis weights hbasis
            (degree - (split.val + 1)) pair.2))).val = _
    rw [positiveTensorDegreeEquiv_symm_basis, TensorProduct.map_tmul]
    simp only [Submodule.coe_subtype, TauCeti.coe_homogeneousMonomialBasis,
      homogeneousFiberBasis_apply]
  have hvalue := LinearMap.congr_fun hmap (polynomial ⊗ₜ[K] vector)
  change ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.of family split (polynomial ⊗ₜ[K] vector))).val =
      TensorProduct.map _ _ (polynomial ⊗ₜ[K] vector) at hvalue
  rw [TensorProduct.map_tmul] at hvalue
  exact hvalue

end Schubert.FiniteGroupCharacters
