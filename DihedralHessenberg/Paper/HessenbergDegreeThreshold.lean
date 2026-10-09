import DihedralHessenberg.Paper.HessenbergClassification
import DihedralHessenberg.Paper.HessenbergInversions
import DihedralHessenberg.Dihedral.InversionBounds

/-! # The low-degree Hessenberg threshold

If H contains at least 2h roots, all reflection roots of length at most 2h-1
belong to H. H-length agrees with canonical length through h and is at least h
for elements of canonical length at least h.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Every root in a layer below h belongs to an ideal containing at least 2h roots. -/
theorem mem_roots_of_val_lt_twice_half (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (index : PositiveRootIndex n)
    (hindex : index.val < 2 * half) : index ∈ ideal.roots := by
  obtain (hprefix | ⟨hodd, _, hother⟩) := ideal.root_membership_classification
  · exact (hprefix index).mpr (by omega)
  · have hparity := Nat.odd_iff.mp hodd
    exact (hother index).mpr (Or.inl (by omega))

/-- All right inversions of an element of length at most h belong to H. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.right_inversions_below_half (ideal :
  HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (element : DihedralGroup n)
    (hlength : Schubert.Dihedral.length n hthree element ≤ half) :
    rightInversions n hthree element ⊆ ideal.roots := by
  intro index hindex
  have hbound := _root_.Schubert.Dihedral.IndexedRoots.length_bound_at_inversion n hthree element
    index hindex
  rw [length_rootReflection] at hbound
  apply ideal.mem_roots_of_val_lt_twice_half half hhalf index
  omega

/-- H-length equals canonical length for every element of length at most h. -/
theorem length_eq_coxeter_length_of_le_half (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (element : DihedralGroup n)
    (hlength : Schubert.Dihedral.length n hthree element ≤ half) :
    ideal.length element = Schubert.Dihedral.length n hthree element := by
  classical
  have hsubset := ideal.right_inversions_below_half half hhalf element hlength
  rw [length, inversions, Finset.inter_eq_right.mpr hsubset, card_rightInversions]

/-- Every element of canonical length at least h has H-length at least h. -/
theorem half_le_length_of_half_le_coxeter_length (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (element : DihedralGroup n)
    (hlength : half ≤ Schubert.Dihedral.length n hthree element) : half ≤ ideal.length element := by
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  let position := word.length - half
  let suffix := (coxeterSystem n hthree).wordProd (word.drop position)
  have hsuffixLength : Schubert.Dihedral.length n hthree suffix = half := by
    change (coxeterSystem n hthree).length
      ((coxeterSystem n hthree).wordProd (word.drop position)) = half
    rw [(hword.drop position).eq, List.length_drop]
    change half ≤ (coxeterSystem n hthree).length
      ((coxeterSystem n hthree).wordProd word) at hlength
    rw [hword.eq] at hlength
    dsimp only [position]
    omega
  have hsuffixRoots := ideal.right_inversions_below_half half hhalf
    suffix hsuffixLength.le
  have hsuffixInversions : rightInversions n hthree suffix ⊆
      ideal.inversions ((coxeterSystem n hthree).wordProd word) := by
    intro index hindex
    rw [ideal.mem_inversions]
    refine ⟨hsuffixRoots hindex, ?_⟩
    apply (mem_rightInversions n hthree _ index).mp
    exact rightInversions_wordProd_drop_subset n hthree hword position hindex
  have hcount := Finset.card_le_card hsuffixInversions
  rw [card_rightInversions, hsuffixLength] at hcount
  exact hcount

/-- Below h, an H-degree fiber is exactly the corresponding canonical length fiber. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.length_eq_coxeter_below_half (ideal :
  HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (degree : ℕ) (hdegree : degree < half)
    (element : DihedralGroup n) :
    ideal.length element = degree ↔ Schubert.Dihedral.length n hthree element = degree := by
  constructor
  · intro heq
    by_cases hlength : Schubert.Dihedral.length n hthree element ≤ half
    · rwa [ideal.length_eq_coxeter_length_of_le_half half hhalf element hlength] at heq
    · have hbound := ideal.half_le_length_of_half_le_coxeter_length half hhalf element
        (by omega)
      omega
  · intro heq
    rw [ideal.length_eq_coxeter_length_of_le_half half hhalf element (by omega), heq]

end Schubert.DihedralSplines.HessenbergSpace
