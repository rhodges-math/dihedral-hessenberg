import Schubert.FiniteGroupCharacters.TensorAugmentation
import Schubert.FiniteGroupCharacters.TensorPieceFinite

/-! # Positive scalar-degree fibers in ordinary tensor components -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- The augmentation kernel in each total degree is exactly its positive scalar basis fiber. -/
theorem positive_tensor_piece {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    positiveTensor (K := K) (P := P) (Q := Q) ⊓ tensorPiece pieces degree =
      Submodule.span K (Set.range fun index :
        {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree ∧ pair.1 ≠ 0} =>
        ((MvPolynomial.basisMonomials P K).tensorProduct basis) index.val) := by
  classical
  let := tensor_degree_fiber_finite (K := K) (P := P) weights degree
  let : Fintype {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree} :=
    Fintype.ofFinite _
  let restricted := tensorPieceBasis (P := P) pieces basis weights hbasis degree
  apply le_antisymm
  · intro value hvalue
    let homogeneous : tensorPiece (P := P) pieces degree := ⟨value, hvalue.2⟩
    have hzero : tensorAugmentation value = 0 := by
      rw [← LinearMap.mem_ker, tensorAugmentation_ker basis]
      exact hvalue.1
    have hexpansion := congrArg (tensorPiece (P := P) pieces degree).subtype
      (restricted.sum_repr homogeneous)
    simp only [map_sum, map_smul] at hexpansion
    change ∑ index, restricted.repr homogeneous index • (restricted index).val = value at hexpansion
    rw [← hexpansion]
    apply Submodule.sum_mem
    intro index _
    by_cases hexponent : index.val.1 = 0
    · have hcoordinate : restricted.repr homogeneous index = 0 := by
        rw [tensorPieceBasis_repr]
        have hpair : index.val = (0, index.val.2) := Prod.ext hexponent rfl
        rw [hpair, ← tensorAugmentation_coordinate basis value index.val.2, hzero,
          map_zero, Finsupp.zero_apply]
      rw [hcoordinate, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨⟨index.val, index.property, hexponent⟩, ?_⟩
      rw [tensorPieceBasis_apply]
      exact (Module.Basis.tensorProduct_apply' (MvPolynomial.basisMonomials P K)
        basis index.val)
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    constructor
    · apply Submodule.subset_span
      refine ⟨index.val.1, basis index.val.2, index.property.2, ?_⟩
      exact Module.Basis.tensorProduct_apply' _ _ _
    · have hmember := (tensorPieceBasis (P := P) pieces basis weights hbasis degree
        ⟨index.val, index.property.1⟩).property
      rw [tensorPieceBasis_apply] at hmember
      change ((MvPolynomial.basisMonomials P K).tensorProduct basis) index.val ∈
        tensorPiece pieces degree
      rw [Module.Basis.tensorProduct_apply']
      exact hmember

end Schubert.FiniteGroupCharacters
