import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.DihedralSplines.HessenbergCount

/-! # Classification of vector Hessenberg ideals -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- The real cone compares equal vectors and strictly increasing alternating layers. -/
theorem rootOrder_layers {n : ℕ} {hthree : 3 ≤ n} (alpha beta : PositiveRoot n) :
    RootOrder n hthree alpha beta ↔ alpha = beta ∨ alpha.index.val / 2 < beta.index.val / 2 := by
  rw [rootOrder_indices, rootLE_iff_eq_or_layer_lt]
  exact or_congr (positiveRootEquiv n).symm.injective.eq_iff Iff.rfl

namespace HessenbergIdeal

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Each vector ideal is a numbered initial segment or the other final-layer choice. -/
theorem classification (ideal : HessenbergIdeal n hthree) :
    (∃ size : ℕ, 2 ≤ size ∧ size ≤ n ∧
      ideal.carrier = positiveRoot n '' {index : PositiveRootIndex n | index.val < size}) ∨
    (∃ layer : ℕ, 2 ≤ layer ∧ layer ≤ n / 2 ∧
      ideal.carrier = positiveRoot n '' {index : PositiveRootIndex n |
        index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1}) := by
  rcases ideal.indexed.paper_family_classification with ⟨size, htwo, hbound, hmem⟩ |
    ⟨layer, htwo, hbound, hmem⟩
  · refine Or.inl ⟨size, htwo, hbound, ?_⟩
    have hroots : (ideal.indexed.roots : Set (PositiveRootIndex n)) =
        {index | index.val < size} := Set.ext hmem
    rw [← ideal.image_indexed, hroots]
  · refine Or.inr ⟨layer, htwo, hbound, ?_⟩
    have hroots : (ideal.indexed.roots : Set (PositiveRootIndex n)) =
        {index | index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1} := Set.ext hmem
    rw [← ideal.image_indexed, hroots]

/-- Every allowed numbered initial segment is a vector Hessenberg ideal. -/
theorem exists_initial (n : ℕ) (hthree : 3 ≤ n) (size : ℕ)
    (htwo : 2 ≤ size) (hbound : size ≤ n) :
    ∃ ideal : HessenbergIdeal n hthree, ideal.carrier.ncard = size ∧
      ideal.carrier = positiveRoot n '' {index : PositiveRootIndex n | index.val < size} := by
  obtain ⟨indexed, hcard, hmem⟩ :=
    HessenbergSpace.exists_initial_segment n hthree size htwo hbound
  refine ⟨ofIndexed indexed, ?_, ?_⟩
  · rw [ncard_indexed, indexed_ofIndexed]
    exact hcard
  · have hroots : (indexed.roots : Set (PositiveRootIndex n)) =
        {index | index.val < size} := Set.ext hmem
    rw [← image_indexed, indexed_ofIndexed, hroots]

/-- Every allowed other-root final-layer choice is a vector Hessenberg ideal. -/
theorem exists_other (n : ℕ) (hthree : 3 ≤ n) (layer : ℕ)
    (htwo : 2 ≤ layer) (hbound : layer ≤ n / 2) :
    ∃ ideal : HessenbergIdeal n hthree, ideal.carrier.ncard = 2 * layer - 1 ∧
      ideal.carrier = positiveRoot n '' {index : PositiveRootIndex n |
        index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1} := by
  obtain ⟨indexed, hcard, hmem⟩ :=
    HessenbergSpace.exists_other_root_final_layer n hthree layer htwo hbound
  refine ⟨ofIndexed indexed, ?_, ?_⟩
  · rw [ncard_indexed, indexed_ofIndexed]
    exact hcard
  · have hroots : (indexed.roots : Set (PositiveRootIndex n)) =
        {index | index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1} := Set.ext hmem
    rw [← image_indexed, indexed_ofIndexed, hroots]

/-- There are n plus floor(n/2) minus two vector Hessenberg ideals. -/
theorem natCard (n : ℕ) (hthree : 3 ≤ n) :
    Nat.card (HessenbergIdeal n hthree) = n + n / 2 - 2 :=
  (Nat.card_congr indexedEquiv).trans (HessenbergSpace.natCard n hthree)

end HessenbergIdeal

end Schubert.DihedralSplines
