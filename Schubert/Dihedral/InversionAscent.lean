import Schubert.Dihedral.Inversions

/-! # Canonical inversion updates under a simple left ascent -/

namespace Schubert.Dihedral

private theorem reduced_cons_of_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) {word : List (Fin 2)} (hword : IsReduced n hthree word)
    (hascent : length n hthree
      (simpleReflection n simple * (coxeterSystem n hthree).wordProd word) =
        length n hthree ((coxeterSystem n hthree).wordProd word) + 1) :
    IsReduced n hthree (simple :: word) := by
  rw [isReduced_iff_length_wordProd] at hword ⊢
  rw [CoxeterSystem.wordProd_cons, coxeterSystem_simple, hascent, hword]
  rfl

/-- A simple left ascent inserts the conjugated simple reflection into right inversions. -/
theorem image_rightInversions_simple_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    (rightInversions n hthree (simpleReflection n simple * element)).image rootReflection =
      insert (element⁻¹ * simpleReflection n simple * element)
        ((rightInversions n hthree element).image rootReflection) := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  have hcons := reduced_cons_of_left_ascent n hthree simple hword hascent
  have hseq := image_rightInversions_eq_invSeq n hthree hcons
  rw [CoxeterSystem.wordProd_cons, coxeterSystem_simple] at hseq
  rw [hseq, image_rightInversions_eq_invSeq n hthree hword,
    CoxeterSystem.rightInvSeq, List.toFinset_cons, coxeterSystem_simple]

/-- The newly inserted conjugated simple reflection is absent from the previous inversions. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.conjugate_simple_not_mem (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    element⁻¹ * simpleReflection n simple * element ∉
      (rightInversions n hthree element).image rootReflection := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  have hcons := reduced_cons_of_left_ascent n hthree simple hword hascent
  have hnodup := hcons.nodup_rightInvSeq
  rw [CoxeterSystem.rightInvSeq, List.nodup_cons, coxeterSystem_simple] at hnodup
  rw [image_rightInversions_eq_invSeq n hthree hword, List.mem_toFinset]
  exact hnodup.1

/-- A simple left ascent conjugates previous left inversions and inserts the simple reflection. -/
theorem image_leftInversions_simple_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    (leftInversions n hthree (simpleReflection n simple * element)).image rootReflection =
      insert (simpleReflection n simple)
        (((leftInversions n hthree element).image rootReflection).image
          (MulAut.conj (simpleReflection n simple))) := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  have hcons := reduced_cons_of_left_ascent n hthree simple hword hascent
  have hseq := image_leftInversions_eq_invSeq n hthree hcons
  rw [CoxeterSystem.wordProd_cons, coxeterSystem_simple] at hseq
  rw [hseq, image_leftInversions_eq_invSeq n hthree hword,
    CoxeterSystem.leftInvSeq, List.toFinset_cons, coxeterSystem_simple]
  congr 1
  ext reflection
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]

/-- The inserted simple reflection is absent from the conjugated previous left inversions. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.simple_not_mem_conjugate (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) :
    simpleReflection n simple ∉
      ((leftInversions n hthree element).image rootReflection).image
        (MulAut.conj (simpleReflection n simple)) := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  have hcons := reduced_cons_of_left_ascent n hthree simple hword hascent
  have hnodup := hcons.nodup_leftInvSeq
  rw [CoxeterSystem.leftInvSeq, List.nodup_cons, coxeterSystem_simple] at hnodup
  rw [image_leftInversions_eq_invSeq n hthree hword]
  simp only [Finset.mem_image, List.mem_toFinset]
  rintro ⟨reflection, hreflection, heq⟩
  exact hnodup.1 (List.mem_map.mpr ⟨reflection, hreflection, heq⟩)

end Schubert.Dihedral
