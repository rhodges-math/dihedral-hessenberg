import DihedralHessenberg.Paper.Hessenberg
import DihedralHessenberg.Dihedral.Inversions

/-! # Hessenberg inversions and Hessenberg length

The paper's H-inversions are the right canonical inversions belonging to H.
Their cardinality is the H-length, bounded by both canonical length and |H|.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The positive roots in H whose reflections decrease canonical length on the right. -/
noncomputable def inversions (ideal : HessenbergSpace n hthree) (element : DihedralGroup n) :
    Finset (PositiveRootIndex n) := by
  classical
  exact ideal.roots ∩ rightInversions n hthree element

/-- The H-length of an element is the number of its H-inversions. -/
noncomputable def length (ideal : HessenbergSpace n hthree) (element : DihedralGroup n) : ℕ :=
  (ideal.inversions element).card

/-- H-inversion membership is root membership together with a right length decrease. -/
theorem mem_inversions (ideal : HessenbergSpace n hthree) (element : DihedralGroup n)
    (index : PositiveRootIndex n) :
    index ∈ ideal.inversions element ↔ index ∈ ideal.roots ∧
      Schubert.Dihedral.length n hthree (element * rootReflection index) <
        Schubert.Dihedral.length n hthree element := by
  classical
  simp only [inversions, Finset.mem_inter, mem_rightInversions]

/-- Every H-inversion belongs to H. -/
theorem inversions_subset_roots (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) : ideal.inversions element ⊆ ideal.roots := by
  classical
  exact Finset.inter_subset_left

/-- Every H-inversion is a canonical right inversion. -/
theorem inversions_subset_rightInversions (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ideal.inversions element ⊆ rightInversions n hthree element := by
  classical
  exact Finset.inter_subset_right

/-- H-length is at most canonical Coxeter length. -/
theorem length_le_coxeter_length (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ideal.length element ≤ Schubert.Dihedral.length n hthree element :=
  (Finset.card_le_card (ideal.inversions_subset_rightInversions element)).trans_eq
    (card_rightInversions n hthree element)

/-- H-length is at most the number of roots in H. -/
theorem length_le_card_roots (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) : ideal.length element ≤ ideal.roots.card :=
  Finset.card_le_card (ideal.inversions_subset_roots element)

/-- The identity has no H-inversions. -/
theorem inversions_one (ideal : HessenbergSpace n hthree) : ideal.inversions 1 = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro index hindex
  have hlt := ((ideal.mem_inversions 1 index).mp hindex).2
  rw [length_one] at hlt
  exact Nat.not_lt_zero _ hlt

/-- The identity has H-length zero. -/
theorem length_one (ideal : HessenbergSpace n hthree) : ideal.length 1 = 0 := by
  rw [length, ideal.inversions_one, Finset.card_empty]

/-- For the full positive-root ideal, H-inversions are all right inversions. -/
theorem inversions_eq_rightInversions (ideal : HessenbergSpace n hthree)
    (hfull : ideal.roots = Finset.univ) (element : DihedralGroup n) :
    ideal.inversions element = rightInversions n hthree element := by
  classical
  rw [inversions, hfull, Finset.univ_inter]

/-- For the full positive-root ideal, H-length is canonical Coxeter length. -/
theorem length_eq_coxeter_length (ideal : HessenbergSpace n hthree)
    (hfull : ideal.roots = Finset.univ) (element : DihedralGroup n) :
    ideal.length element = Schubert.Dihedral.length n hthree element := by
  rw [length, ideal.inversions_eq_rightInversions hfull, card_rightInversions]

end Schubert.DihedralSplines.HessenbergSpace
