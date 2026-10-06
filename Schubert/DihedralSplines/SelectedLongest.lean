import Schubert.Dihedral.RootSubsetCard
import Schubert.Dihedral.LongestReversal
import Schubert.DihedralSplines.HessenbergSymmetry

/-! # Longest-element complementation for selected inversion sets -/

namespace Schubert.Dihedral

/-- Longest multiplication complements the right inversion vectors inside positive roots. -/
theorem rightInversionSet_longest_mul (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    rightInversionSet n (longestElement n hthree * element) =
      positiveRoots n \ rightInversionSet n element := by
  classical
  ext alpha
  by_cases hpositive : alpha ∈ positiveRoots n
  · obtain ⟨index, rfl⟩ := hpositive
    rw [Set.mem_sdiff, mem_rightInversionSet n hthree, mem_rightInversionSet n hthree]
    change index ∈ rightInversions n hthree
      ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) * element) ↔ _
    rw [rightInversions_alternatingWord_top_mul, Finset.mem_compl]
    simp only [positiveRoots, Set.mem_range, exists_apply_eq_apply, true_and]
  · simp only [rightInversionSet, Set.mem_ofPred_eq, Set.mem_sdiff, hpositive, false_and]

namespace RootSubset

/-- Longest multiplication complements selected inversion vectors inside the selected carrier. -/
theorem inversions_longest_mul {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (element : DihedralGroup n) :
    selected.inversions (longestElement n hthree * element) =
      selected.carrier \ selected.inversions element := by
  rw [inversions, rightInversionSet_longest_mul]
  ext alpha
  constructor
  · rintro ⟨hselected, _, hnegative⟩
    exact ⟨hselected, fun hinversion => hnegative hinversion.2⟩
  · rintro ⟨hselected, hinversion⟩
    exact ⟨hselected, selected.positive hselected,
      fun hnegative => hinversion ⟨hselected, hnegative⟩⟩

/-- The selected inversion counts of longest-related vertices sum to selected root cardinality. -/
theorem length_longest_add {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (element : DihedralGroup n) :
    selected.length (longestElement n hthree * element) + selected.length element =
      selected.carrier.ncard := by
  rw [length, selected.inversions_longest_mul]
  exact Set.ncard_sdiff_add_ncard_of_subset (fun _ hmem => hmem.1) selected.finite

end RootSubset

end Schubert.Dihedral
