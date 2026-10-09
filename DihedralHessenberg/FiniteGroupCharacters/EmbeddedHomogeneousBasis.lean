import DihedralHessenberg.Splines.HomogeneousBasis

/-! # Homogeneous basis restriction through an injective linear map

The domain need not carry a named grading. Its vectors whose images belong to one
ambient degree have a basis obtained by selecting the appropriate basis vectors.
-/

noncomputable section

namespace Schubert.FiniteGroupCharacters

open Schubert.Splines

/-- An embedded homogeneous basis spans each comapped ambient degree by its degree fiber. -/
theorem _root_.Schubert.FiniteGroupCharacters.EmbeddedBasis.piece_eq_span_degree
    {K M N I D : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [DecidableEq D]
    (pieces : D → Submodule K N) [DirectSum.Decomposition pieces]
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, embedding (basis index) ∈ pieces (degrees index)) (degree : D) :
    (pieces degree).comap embedding = Submodule.span K
      (Set.range fun index : {index // degrees index = degree} => basis index) := by
  classical
  have hprojection (index : I) :
      homogeneousProjection pieces degree (embedding (basis index)) =
        if degrees index = degree then embedding (basis index) else 0 := by
    split_ifs with hequal
    · exact homogeneousProjection_of_mem pieces degree (hequal ▸ hbasis index)
    · exact homogeneousProjection_of_mem_ne pieces degree (degrees index)
        (hbasis index) hequal
  apply le_antisymm
  · intro value hvalue
    have hfiltered : value = ∑ index ∈ (basis.repr value).support,
        if degrees index = degree then basis.repr value index • basis index else 0 := by
      apply hinjective
      calc
        embedding value = homogeneousProjection pieces degree (embedding value) :=
          (homogeneousProjection_of_mem pieces degree hvalue).symm
        _ = ∑ index ∈ (basis.repr value).support,
            basis.repr value index • homogeneousProjection pieces degree
              (embedding (basis index)) := by
          conv_lhs =>
            rw [← basis.linearCombination_repr value, Finsupp.linearCombination_apply,
              Finsupp.sum, map_sum, map_sum]
          simp only [map_smul]
        _ = embedding (∑ index ∈ (basis.repr value).support,
            if degrees index = degree then basis.repr value index • basis index else 0) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro index _
          by_cases hequal : degrees index = degree <;>
            simp [hprojection, hequal]
    rw [hfiltered]
    apply Submodule.sum_mem
    intro index _
    by_cases hequal : degrees index = degree
    · rw [ite_eq_left hequal]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨index, hequal⟩, rfl⟩)
    · rw [ite_eq_right hequal]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    change embedding (basis index.val) ∈ pieces degree
    have hmember := hbasis index.val
    rw [index.property] at hmember
    exact hmember

/-- Restrict an embedded homogeneous basis to a comapped ambient degree. -/
theorem exists_embedded_homogeneousPiece_basis
    {K M N I D : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [DecidableEq D]
    (pieces : D → Submodule K N) [DirectSum.Decomposition pieces]
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, embedding (basis index) ∈ pieces (degrees index)) (degree : D) :
    ∃ restrictedBasis : Module.Basis {index // degrees index = degree} K
        ((pieces degree).comap embedding),
      ∀ index, (restrictedBasis index : M) = basis index.val := by
  classical
  let independent := basis.linearIndependent.comp
    (Subtype.val : {index // degrees index = degree} → I) Subtype.val_injective
  let equivalence := LinearEquiv.ofEq _ _
    (_root_.Schubert.FiniteGroupCharacters.EmbeddedBasis.piece_eq_span_degree pieces embedding
      hinjective
      basis degrees hbasis degree).symm
  refine ⟨(Module.Basis.span independent).map equivalence, fun index => ?_⟩
  rw [Module.Basis.map_apply]
  change (Module.Basis.span independent index : M) = basis index.val
  exact Module.Basis.coe_span_apply independent index

/-- The rank of a comapped homogeneous degree counts its embedded basis degree fiber. -/
theorem embedded_homogeneousPiece_finrank
    {K M N I D : Type*} [CommRing K] [StrongRankCondition K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [DecidableEq D]
    (pieces : D → Submodule K N) [DirectSum.Decomposition pieces]
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, embedding (basis index) ∈ pieces (degrees index)) (degree : D) :
    Module.finrank K ((pieces degree).comap embedding) =
      Nat.card {index // degrees index = degree} := by
  obtain ⟨restrictedBasis, _⟩ := exists_embedded_homogeneousPiece_basis
    pieces embedding hinjective basis degrees hbasis degree
  exact Module.finrank_eq_nat_card_basis restrictedBasis

/-- A finite degree fiber makes the comapped degree finite-dimensional. -/
theorem embedded_homogeneousPiece_finite
    {K M N I D : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [DecidableEq D]
    (pieces : D → Submodule K N) [DirectSum.Decomposition pieces]
    (embedding : M →ₗ[K] N) (hinjective : Function.Injective embedding)
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, embedding (basis index) ∈ pieces (degrees index)) (degree : D)
    [Finite {index // degrees index = degree}] :
    Module.Finite K ((pieces degree).comap embedding) := by
  obtain ⟨restrictedBasis, _⟩ := exists_embedded_homogeneousPiece_basis
    pieces embedding hinjective basis degrees hbasis degree
  exact Module.Finite.of_basis restrictedBasis

end Schubert.FiniteGroupCharacters
