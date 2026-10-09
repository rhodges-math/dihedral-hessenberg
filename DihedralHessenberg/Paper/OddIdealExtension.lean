import DihedralHessenberg.Paper.HessenbergVectorClassification
import DihedralHessenberg.Paper.DominanceEven

/-! # Completing the final layer of a proper odd-cardinality ideal -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- A proper odd ideal extends by exactly one vector to its full initial final layer. -/
theorem odd_extension {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    ∃ (larger : HessenbergIdeal n hthree) (delta : PositiveRoot n),
      larger.carrier.ncard = 2 * half + 2 ∧ delta.val ∉ ideal.carrier ∧
        larger.carrier = insert delta.val ideal.carrier ∧
          larger.carrier = positiveRoot n ''
            {index : PositiveRootIndex n | index.val < 2 * half + 2} := by
  have hbound := ideal.card_lt hproper
  have htwo := ideal.indexed.two_le_card
  have hindexed : ideal.indexed.roots.card = 2 * half + 1 := by
    rw [← ideal.ncard_indexed, hcard]
  obtain ⟨larger, hlargeCard, hlargeCarrier⟩ :=
    exists_initial n hthree (2 * half + 2) (by omega) (by omega)
  have hcompletion : ∃ delta : PositiveRootIndex n, delta ∉ ideal.indexed.roots ∧
      insert delta (ideal.indexed.roots : Set (PositiveRootIndex n)) =
        {index : PositiveRootIndex n | index.val < 2 * half + 2} := by
    rcases ideal.indexed.root_membership_classification with hprefix | ⟨_, _, hother⟩
    · let delta : PositiveRootIndex n := ⟨2 * half + 1, by omega⟩
      refine ⟨delta, ?_, ?_⟩
      · rw [hprefix, hindexed]
        simp only [delta]
        omega
      · ext index
        simp only [Set.mem_insert_iff, Finset.mem_coe, Set.mem_ofPred_eq,
          hprefix, hindexed, Fin.ext_iff, delta]
        omega
    · let delta : PositiveRootIndex n := ⟨2 * half, by omega⟩
      refine ⟨delta, ?_, ?_⟩
      · rw [hother, hindexed]
        simp only [delta]
        omega
      · ext index
        simp only [Set.mem_insert_iff, Finset.mem_coe, Set.mem_ofPred_eq,
          hother, hindexed, Fin.ext_iff, delta]
        omega
  obtain ⟨delta, hmissing, hcompletion⟩ := hcompletion
  refine ⟨larger, positiveRootEquiv n delta, hlargeCard, ?_, ?_, hlargeCarrier⟩
  · rw [positiveRootEquiv_val]
    exact fun hselected => hmissing ((ideal.mem_indexed delta).mpr hselected)
  · rw [positiveRootEquiv_val, ← ideal.image_indexed, ← Set.image_insert_eq, hcompletion]
    exact hlargeCarrier

end Schubert.DihedralSplines.HessenbergIdeal
