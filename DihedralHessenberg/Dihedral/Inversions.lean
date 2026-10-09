import DihedralHessenberg.Dihedral.RootReflections

/-! # Canonical inversion sets of dihedral elements

The indexed inversion sets map bijectively to the canonical inversion sequences
of any reduced word. Consequently both inversion sets have cardinality equal
to canonical length, and every dihedral element has length at most n.
-/

namespace Schubert.Dihedral

/-- Left indexed inversions enumerate the canonical left inversion sequence. -/
theorem image_leftInversions_eq_invSeq (n : ℕ) (hthree : 3 ≤ n)
    {word : List (Fin 2)} (hword : IsReduced n hthree word) :
    (leftInversions n hthree ((coxeterSystem n hthree).wordProd word)).image rootReflection =
      ((coxeterSystem n hthree).leftInvSeq word).toFinset := by
  classical
  ext reflection
  rw [Finset.mem_image, List.mem_toFinset,
    (coxeterSystem n hthree).mem_leftInvSeq_iff_isLeftInversion hword]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact ⟨rootReflection_isReflection n hthree index,
      (mem_leftInversions n hthree _ index).mp hindex⟩
  · rintro ⟨hreflection, hlength⟩
    obtain ⟨index, hindex⟩ := (isReflection_iff_exists_rootReflection n hthree reflection).mp
      hreflection
    refine ⟨index, ?_, hindex⟩
    rw [mem_leftInversions, hindex]
    exact hlength

/-- Right indexed inversions enumerate the canonical right inversion sequence. -/
theorem image_rightInversions_eq_invSeq (n : ℕ) (hthree : 3 ≤ n)
    {word : List (Fin 2)} (hword : IsReduced n hthree word) :
    (rightInversions n hthree ((coxeterSystem n hthree).wordProd word)).image rootReflection =
      ((coxeterSystem n hthree).rightInvSeq word).toFinset := by
  classical
  ext reflection
  rw [Finset.mem_image, List.mem_toFinset,
    (coxeterSystem n hthree).mem_rightInvSeq_iff_isRightInversion hword]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact ⟨rootReflection_isReflection n hthree index,
      (mem_rightInversions n hthree _ index).mp hindex⟩
  · rintro ⟨hreflection, hlength⟩
    obtain ⟨index, hindex⟩ := (isReflection_iff_exists_rootReflection n hthree reflection).mp
      hreflection
    refine ⟨index, ?_, hindex⟩
    rw [mem_rightInversions, hindex]
    exact hlength

/-- The number of left inversions equals canonical Coxeter length. -/
theorem card_leftInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (leftInversions n hthree element).card = length n hthree element := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  rw [← Finset.card_image_of_injective _ (rootReflection_injective n),
    image_leftInversions_eq_invSeq n hthree hword,
    List.toFinset_card_of_nodup hword.nodup_leftInvSeq,
    CoxeterSystem.length_leftInvSeq]
  exact hword.symm

/-- The number of right inversions equals canonical Coxeter length. -/
theorem card_rightInversions (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (rightInversions n hthree element).card = length n hthree element := by
  classical
  obtain ⟨word, hword, rfl⟩ := (coxeterSystem n hthree).exists_isReduced element
  rw [← Finset.card_image_of_injective _ (rootReflection_injective n),
    image_rightInversions_eq_invSeq n hthree hword,
    List.toFinset_card_of_nodup hword.nodup_rightInvSeq,
    CoxeterSystem.length_rightInvSeq]
  exact hword.symm

/-- Every element of the n-gon dihedral group has canonical length at most n. -/
theorem length_le_polygon_parameter (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    length n hthree element ≤ n := by
  rw [← card_leftInversions n hthree element]
  simpa only [Fintype.card_fin] using (leftInversions n hthree element).card_le_univ

/-- Inverting an element exchanges its left and right indexed inversions. -/
theorem rightInversions_inv_eq_leftInversions (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    rightInversions n hthree element⁻¹ = leftInversions n hthree element := by
  classical
  ext index
  rw [mem_rightInversions, mem_leftInversions, length_inv]
  have hlength : length n hthree (element⁻¹ * rootReflection index) =
      length n hthree (rootReflection index * element) := by
    rw [← length_inv n hthree (rootReflection index * element), mul_inv_rev,
      (rootReflection_isReflection n hthree index).inv]
  rw [hlength]

end Schubert.Dihedral
