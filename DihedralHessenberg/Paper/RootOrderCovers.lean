import DihedralHessenberg.Paper.HessenbergVectorClassification

/-! # The Hasse diagram of the root poset

With the alternating numbering, the positive roots `α_{2k+1}` and `α_{2k+2}` form the `k`-th layer
of the root poset; for odd `n` the last layer is the single root `α_n`. One root lies strictly below
another exactly when its layer is lower, and it is covered exactly by the roots of the next layer:
consecutive layers are joined by all possible edges of the Hasse diagram.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- One positive root lies strictly below another exactly when its layer is lower. -/
theorem rootOrder_lt_iff (alpha beta : PositiveRoot n) :
    @LT.lt _ (rootOrder n hthree).toLT alpha beta ↔
      alpha.index.val / 2 < beta.index.val / 2 := by
  change RootOrder n hthree alpha beta ∧ ¬RootOrder n hthree beta alpha ↔ _
  rw [rootOrder_layers, rootOrder_layers]
  constructor
  · rintro ⟨hle | hlt, hnot⟩
    · exact (hnot (Or.inl hle.symm)).elim
    · exact hlt
  · intro hlt
    refine ⟨Or.inr hlt, ?_⟩
    rintro (heq | hgt)
    · rw [heq] at hlt
      exact lt_irrefl _ hlt
    · omega

/-- A positive root is covered exactly by the positive roots of the next layer. -/
theorem rootOrder_covBy_iff (alpha beta : PositiveRoot n) :
    @CovBy _ (rootOrder n hthree).toLT alpha beta ↔
      beta.index.val / 2 = alpha.index.val / 2 + 1 := by
  constructor
  · rintro ⟨hlt, hnone⟩
    rw [rootOrder_lt_iff] at hlt
    by_contra hne
    -- the first root of the next layer lies strictly between
    have hbound : 2 * (alpha.index.val / 2 + 1) < n := by
      have := beta.index.isLt
      omega
    let middle : PositiveRoot n := positiveRootEquiv n ⟨2 * (alpha.index.val / 2 + 1), hbound⟩
    have hmiddle : middle.index.val = 2 * (alpha.index.val / 2 + 1) := by
      simp only [middle, PositiveRoot.index_equiv]
    apply hnone (c := middle)
    · rw [rootOrder_lt_iff, hmiddle]
      omega
    · rw [rootOrder_lt_iff, hmiddle]
      omega
  · intro hnext
    refine ⟨(rootOrder_lt_iff alpha beta).mpr (by omega), fun middle hlow hhigh => ?_⟩
    rw [rootOrder_lt_iff] at hlow hhigh
    omega

/-- The layers below the top layer contain two roots each, and the top layer of an odd number of
roots contains only the last root. -/
theorem layer_card (layer : ℕ) :
    {alpha : PositiveRoot n | alpha.index.val / 2 = layer}.ncard =
      if 2 * layer + 1 < n then 2 else if 2 * layer < n then 1 else 0 := by
  classical
  have himage : {alpha : PositiveRoot n | alpha.index.val / 2 = layer} =
      positiveRootEquiv n '' {index : PositiveRootIndex n | index.val / 2 = layer} := by
    ext alpha
    constructor
    · intro halpha
      exact ⟨alpha.index, halpha, (positiveRootEquiv n).apply_symm_apply alpha⟩
    · rintro ⟨index, hindex, rfl⟩
      change (positiveRootEquiv n index).index.val / 2 = layer
      rw [PositiveRoot.index_equiv]
      exact hindex
  rw [himage, Set.ncard_image_of_injective _ (positiveRootEquiv n).injective]
  have hset : {index : PositiveRootIndex n | index.val / 2 = layer} =
      ((Finset.univ.filter fun index : PositiveRootIndex n => index.val / 2 = layer) :
        Set (PositiveRootIndex n)) := by
    ext index
    simp
  rw [hset, Set.ncard_coe_finset]
  have hmap : (Finset.univ.filter fun index : PositiveRootIndex n => index.val / 2 = layer).map
      Fin.valEmbedding = (Finset.range n).filter fun value => value / 2 = layer := by
    ext value
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_range]
    constructor
    · rintro ⟨index, hindex, rfl⟩
      exact ⟨index.isLt, hindex⟩
    · rintro ⟨hlt, hvalue⟩
      exact ⟨⟨value, hlt⟩, hvalue, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hmap]
  have hrange : (Finset.range n).filter (fun value => value / 2 = layer) =
      (Finset.range n).filter (fun value => 2 * layer ≤ value ∧ value < 2 * layer + 2) := by
    apply Finset.filter_congr
    intro value _
    omega
  rw [hrange]
  split_ifs with htwo hone
  · have : (Finset.range n).filter (fun value => 2 * layer ≤ value ∧ value < 2 * layer + 2) =
        {2 * layer, 2 * layer + 1} := by
      ext value
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [this, Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  · have : (Finset.range n).filter (fun value => 2 * layer ≤ value ∧ value < 2 * layer + 2) =
        {2 * layer} := by
      ext value
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this, Finset.card_singleton]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro value hvalue
    simp only [Finset.mem_range] at hvalue
    omega

end Schubert.DihedralSplines
