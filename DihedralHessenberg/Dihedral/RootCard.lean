import DihedralHessenberg.Dihedral.RootAxioms
import Mathlib.Data.Set.Card

/-! # Cardinalities of positive and signed root sets -/

namespace Schubert.Dihedral

/-- Alternating numbering gives exactly n positive vectors. -/
theorem positiveRoots_ncard (n : ℕ) : (positiveRoots n).ncard = n := by
  rw [positiveRoots, Set.ncard_range_of_injective (positiveRoot_injective n)]
  simp

/-- The positive and negative vector sets are disjoint. -/
theorem positiveRoots_disjoint_negatives (n : ℕ) :
    Disjoint (positiveRoots n) {vector | -vector ∈ positiveRoots n} := by
  rw [Set.disjoint_left]
  intro vector hpositive hnegative
  obtain ⟨first, rfl⟩ := hpositive
  obtain ⟨second, hsecond⟩ := hnegative
  exact positiveRoot_ne_neg n second first hsecond

/-- The signed unit root system contains exactly twice the polygon parameter vectors. -/
theorem roots_ncard (n : ℕ) : (roots n).ncard = 2 * n := by
  have hpositive : (positiveRoots n).Finite := Set.finite_range _
  have hnegative : {vector : RealPlane | -vector ∈ positiveRoots n}.Finite :=
    (roots_finite n).subset (by intro vector hv; exact Or.inr hv)
  have himage : {vector : RealPlane | -vector ∈ positiveRoots n} =
      Neg.neg '' positiveRoots n := by
    ext vector
    constructor
    · intro hv
      exact ⟨-vector, hv, neg_neg vector⟩
    · rintro ⟨previous, hprevious, hvector⟩
      change -vector ∈ positiveRoots n
      rw [← hvector, neg_neg]
      exact hprevious
  rw [roots, Set.ncard_union_eq (positiveRoots_disjoint_negatives n) hpositive hnegative,
    himage, Set.ncard_image_of_injective _ neg_injective, positiveRoots_ncard]
  omega

end Schubert.Dihedral
