import Schubert.Dihedral.RootInversionSets

/-! # Cardinality transport for positive-vector subsets -/

namespace Schubert.Dihedral

/-- The number of selected vectors equals the number of their selected indices. -/
theorem RootSubset.ncard_indices {n : ℕ} (selected : RootSubset n) :
    selected.carrier.ncard = selected.indicesFinset.card := by
  rw [← selected.image_indices, Set.ncard_image_of_injective _ (positiveRoot_injective n)]
  exact Set.ncard_eq_toFinset_card selected.indices

/-- Geometric right inversions have canonical Coxeter length as their cardinality. -/
theorem ncard_rightInversionSet (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (rightInversionSet n element).ncard = length n hthree element := by
  rw [← image_rightInversions n hthree element,
    Set.ncard_image_of_injective _ (positiveRoot_injective n), Set.ncard_coe_finset,
    card_rightInversions]

/-- Geometric left inversions have canonical Coxeter length as their cardinality. -/
theorem ncard_leftInversionSet (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (leftInversionSet n element).ncard = length n hthree element := by
  rw [← image_leftInversions n hthree element,
    Set.ncard_image_of_injective _ (positiveRoot_injective n), Set.ncard_coe_finset,
    card_leftInversions]

namespace RootSubset

/-- Alternating numbering restricts to the geometric inversions of any selected subset. -/
theorem inversion_indices {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (element : DihedralGroup n) :
    positiveRoot n '' ((selected.indicesFinset ∩ rightInversions n hthree element :
      Finset (PositiveRootIndex n)) : Set (PositiveRootIndex n)) =
        selected.inversions element := by
  classical
  ext alpha
  constructor
  · rintro ⟨index, hindex, rfl⟩
    rw [Finset.mem_coe, Finset.mem_inter] at hindex
    exact ⟨(selected.mem_indicesFinset index).mp hindex.1,
      (mem_rightInversionSet n hthree element index).mpr hindex.2⟩
  · intro hmem
    obtain ⟨index, rfl⟩ := selected.positive hmem.1
    refine ⟨index, ?_, rfl⟩
    rw [Finset.mem_coe, Finset.mem_inter]
    exact ⟨(selected.mem_indicesFinset index).mpr hmem.1,
      (mem_rightInversionSet n hthree element index).mp hmem.2⟩

/-- The selected-root statistic equals the cardinality of its indexed intersection. -/
theorem length_indices {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (element : DihedralGroup n) :
    selected.length element =
      (selected.indicesFinset ∩ rightInversions n hthree element).card := by
  classical
  rw [length, ← selected.inversion_indices hthree element,
    Set.ncard_image_of_injective _ (positiveRoot_injective n), Set.ncard_coe_finset]

end RootSubset

end Schubert.Dihedral
