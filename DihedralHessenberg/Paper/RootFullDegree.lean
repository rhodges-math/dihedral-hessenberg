import DihedralHessenberg.Paper.PaperFull
import DihedralHessenberg.Dihedral.RootSubsetCard

/-! # Full-root inversion degrees -/

namespace Schubert.Dihedral.RootSubset

/-- The full positive-root subset has canonical Coxeter inversion degree. -/
theorem length_full (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (full n).length element = Schubert.Dihedral.length n hthree element := by
  have hsubset : rightInversionSet n element ⊆ positiveRoots n := fun _ hmem => hmem.1
  change (positiveRoots n ∩ rightInversionSet n element).ncard = _
  rw [Set.inter_eq_right.mpr hsubset, ncard_rightInversionSet]

end Schubert.Dihedral.RootSubset
