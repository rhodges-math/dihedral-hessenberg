import Schubert.Dihedral.AlternatingWords

/-! # Length bounds and suffix containment for right inversions

Right inversions have reflection length smaller than twice the element length.
The right inversions of a reduced suffix are contained in those of the full word.
-/

namespace Schubert.Dihedral

/-- A right inversion has reflection length at most twice the element length minus one. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.length_bound_at_inversion (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hindex : index ∈ rightInversions n hthree element) :
    length n hthree (rootReflection index) ≤ 2 * length n hthree element - 1 := by
  have hlt := (mem_rightInversions n hthree element index).mp hindex
  have hbound := (coxeterSystem n hthree).length_mul_le element⁻¹
    (element * rootReflection index)
  rw [inv_mul_cancel_left, CoxeterSystem.length_inv] at hbound
  change length n hthree (rootReflection index) ≤ length n hthree element +
    length n hthree (element * rootReflection index) at hbound
  omega

/-- Right inversions of a reduced suffix are right inversions of the full reduced word. -/
theorem rightInversions_wordProd_drop_subset (n : ℕ) (hthree : 3 ≤ n)
    {word : List (Fin 2)} (hword : IsReduced n hthree word) (position : ℕ) :
    rightInversions n hthree ((coxeterSystem n hthree).wordProd (word.drop position)) ⊆
      rightInversions n hthree ((coxeterSystem n hthree).wordProd word) := by
  intro index hindex
  have hmem : rootReflection index ∈ (coxeterSystem n hthree).rightInvSeq (word.drop position) :=
    ((coxeterSystem n hthree).mem_rightInvSeq_iff_isRightInversion (hword.drop position)).mpr
      ⟨rootReflection_isReflection n hthree index,
        (mem_rightInversions n hthree _ index).mp hindex⟩
  rw [CoxeterSystem.rightInvSeq_drop] at hmem
  have hinversion := ((coxeterSystem n hthree).mem_rightInvSeq_iff_isRightInversion hword).mp
    (List.mem_of_mem_drop hmem)
  exact (mem_rightInversions n hthree _ index).mpr hinversion.2

end Schubert.Dihedral
