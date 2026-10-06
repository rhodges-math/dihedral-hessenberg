import Schubert.FiniteGroupCharacters.TensorSectionProperties
import Schubert.Splines.ArbitraryHomogeneousBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Basis.SMul

/-! # Total homogeneous degree on ordinary polynomial scalar-extension tensors -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- The ordinary tensor degree is spanned by pure tensors of that total degree. -/
def tensorPiece {K P Q : Type*} [CommRing K] [AddCommGroup Q] [Module K Q]
    (pieces : ℕ → Submodule K Q) (degree : ℕ) :
    Submodule K (MvPolynomial P K ⊗[K] Q) :=
  Submodule.span K {value | ∃ (scalarDegree valueDegree : ℕ) (polynomial : MvPolynomial P K)
    (vector : Q), scalarDegree + valueDegree = degree ∧
    polynomial.IsHomogeneous scalarDegree ∧ vector ∈ pieces valueDegree ∧
    value = polynomial ⊗ₜ[K] vector}

/-- A homogeneous lifted polynomial basis identifies exactly the ordinary tensor degree pieces. -/
theorem tensor_piece_map {K P Q M I : Type*} [CommRing K]
    [AddCommGroup Q] [AddCommGroup M] [Module K Q] [Module K M]
    [Module (MvPolynomial P K) M] [IsScalarTower K (MvPolynomial P K) M]
    (sourcePieces : ℕ → Submodule K Q) (targetPieces : ℕ → Submodule K M)
    [DirectSum.Decomposition targetPieces]
    (basis : Module.Basis I K Q) (lifted : Module.Basis I (MvPolynomial P K) M)
    (weights : I → ℕ) (hbasis : ∀ index, basis index ∈ sourcePieces (weights index))
    (hlifted : ∀ index, lifted index ∈ targetPieces (weights index))
    (lift : Q →ₗ[K] M) (hlift : ∀ index, lift (basis index) = lifted index)
    (hhomogeneous : ∀ degree value, value ∈ sourcePieces degree →
      lift value ∈ targetPieces degree)
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) value,
      polynomial.IsHomogeneous scalarDegree → value ∈ targetPieces valueDegree →
      polynomial • value ∈ targetPieces (scalarDegree + valueDegree)) (degree : ℕ) :
    (tensorPiece (P := P) sourcePieces degree).map ((tensorLift lift).restrictScalars K) =
      targetPieces degree := by
  classical
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro value ⟨scalarDegree, valueDegree, polynomial, vector, hdegree, hpoly, hvector, rfl⟩
    change tensorLift lift (polynomial ⊗ₜ[K] vector) ∈ targetPieces degree
    rw [tensorLift_tmul, ← hdegree]
    exact hsmul _ _ _ _ hpoly (hhomogeneous _ _ hvector)
  · let tower := (MvPolynomial.basisMonomials P K).smulTower lifted
    have htower : ∀ pair, tower pair ∈ targetPieces (pair.1.degree + weights pair.2) := by
      intro pair
      rw [Module.Basis.smulTower_apply]
      exact hsmul _ _ _ _ (MvPolynomial.isHomogeneous_monomial _ rfl) (hlifted pair.2)
    rw [Schubert.Splines.HomogeneousBasis.piece_eq_span_degree targetPieces tower
      (fun pair => pair.1.degree + weights pair.2) htower degree]
    apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    refine ⟨MvPolynomial.monomial index.val.1 1 ⊗ₜ[K] basis index.val.2, ?_, ?_⟩
    · apply Submodule.subset_span
      exact ⟨index.val.1.degree, weights index.val.2,
        MvPolynomial.monomial index.val.1 1, basis index.val.2, index.property,
        MvPolynomial.isHomogeneous_monomial _ rfl, hbasis index.val.2, rfl⟩
    · change tensorLift lift (_ ⊗ₜ[K] _) = _
      rw [tensorLift_tmul, hlift]
      change _ = ((MvPolynomial.basisMonomials P K).smulTower lifted) index.val
      rw [Module.Basis.smulTower_apply]
      rfl

end Schubert.FiniteGroupCharacters
