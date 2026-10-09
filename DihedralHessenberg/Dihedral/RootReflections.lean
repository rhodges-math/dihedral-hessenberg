import DihedralHessenberg.Dihedral.CoxeterSystem
import DihedralHessenberg.Dihedral.ReflectionIndex

/-! # Indexed roots and canonical Coxeter reflections

Every indexed root reflection is a Coxeter reflection. Conversely, each Coxeter
reflection is a unique indexed root reflection. Multiplication by such a reflection
lowers canonical length exactly when it descends in strong Bruhat order.
-/

namespace Schubert.Dihedral

private theorem odd_alternating_wordProd (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (halfLength : ℕ) :
    (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord second first (2 * halfLength + 1)) =
      (simpleReflection n first * simpleReflection n second) ^ halfLength *
        simpleReflection n first := by
  rw [CoxeterSystem.alternatingWord_succ, CoxeterSystem.wordProd_concat,
    CoxeterSystem.prod_alternatingWord_eq_mul_pow]
  have heven : Even (2 * halfLength) := ⟨halfLength, by omega⟩
  simp only [ite_eq_left heven, one_mul, coxeterSystem_simple]
  have hhalf : (2 * halfLength) / 2 = halfLength := by omega
  rw [hhalf]

private theorem alternating_reflection_isReflection (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (halfLength : ℕ) :
    (coxeterSystem n hthree).IsReflection
      ((simpleReflection n first * simpleReflection n second) ^ halfLength *
        simpleReflection n first) := by
  let word := CoxeterSystem.alternatingWord first second (2 * (halfLength + 1))
  have hbound : halfLength < 2 * (halfLength + 1) := by omega
  have hlength : halfLength < ((coxeterSystem n hthree).leftInvSeq word).length := by
    simpa only [CoxeterSystem.length_leftInvSeq,
      CoxeterSystem.length_alternatingWord, word] using hbound
  have hmem : ((coxeterSystem n hthree).leftInvSeq word)[halfLength]'hlength ∈
      (coxeterSystem n hthree).leftInvSeq word := List.getElem_mem hlength
  have hvalue := (coxeterSystem n hthree).getElem_leftInvSeq_alternatingWord
    first second (halfLength + 1) halfLength hbound
  rw [hvalue, odd_alternating_wordProd] at hmem
  exact (coxeterSystem n hthree).isReflection_of_mem_leftInvSeq word hmem

/-- Every positive-root reflection is a canonical Coxeter reflection. -/
theorem rootReflection_isReflection (n : ℕ) (hthree : 3 ≤ n) (index : PositiveRootIndex n) :
    (coxeterSystem n hthree).IsReflection (rootReflection index) := by
  by_cases heven : index.val % 2 = 0
  · rw [rootReflection_of_even_index index heven]
    simpa only [simpleReflection_zero, simpleReflection_one, rotation] using
      alternating_reflection_isReflection n hthree 0 1 (index.val / 2)
  · rw [rootReflection_of_odd_index index heven]
    simpa only [simpleReflection_zero, simpleReflection_one] using
      alternating_reflection_isReflection n hthree 1 0 (index.val / 2)

/-- An indexed root reflection is never the identity rotation. -/
theorem rootReflection_ne_one {n : ℕ} (index : PositiveRootIndex n) : rootReflection index ≠ 1 := by
  rw [rootReflection_eq_sr, DihedralGroup.one_def]
  simp

/-- Every canonical Coxeter reflection is the reflection of an indexed positive root. -/
theorem isReflection_iff_exists_rootReflection (n : ℕ) (hthree : 3 ≤ n)
    (reflection : DihedralGroup n) :
    (coxeterSystem n hthree).IsReflection reflection ↔
      ∃ index : PositiveRootIndex n, rootReflection index = reflection := by
  constructor
  · rintro ⟨element, generator, heq⟩
    have hsimple : simpleReflection n generator =
        DihedralGroup.sr (if generator = 0 then 0 else 1) := by
      unfold simpleReflection
      split_ifs <;> rfl
    rw [coxeterSystem_simple, hsimple] at heq
    have hconcrete : ∃ coordinate : ZMod n, reflection = DihedralGroup.sr coordinate := by
      cases element with
      | r coordinate =>
        exact ⟨(if generator = 0 then 0 else 1) - coordinate + -coordinate,
          by simpa only [DihedralGroup.inv_r, DihedralGroup.r_mul_sr,
            DihedralGroup.sr_mul_r] using heq⟩
      | sr coordinate =>
        exact ⟨coordinate - ((if generator = 0 then 0 else 1) - coordinate),
          by simpa only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
            DihedralGroup.r_mul_sr] using heq⟩
    obtain ⟨coordinate, hcoordinate⟩ := hconcrete
    obtain ⟨index, hindex⟩ := exists_rootReflection_eq_sr n hthree coordinate
    exact ⟨index, hindex.trans hcoordinate.symm⟩
  · rintro ⟨index, rfl⟩
    exact rootReflection_isReflection n hthree index

/-- Left reflection multiplication descends in Bruhat order exactly when length decreases. -/
theorem rootReflection_bruhatLE_mul_left_iff (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) (element : DihedralGroup n) :
    BruhatLE n hthree (rootReflection index * element) element ↔
      length n hthree (rootReflection index * element) < length n hthree element := by
  have hreflection := rootReflection_isReflection n hthree index
  constructor
  · intro hcomparison
    apply CoxeterSystem.BruhatLE.length_lt_of_ne hcomparison
    intro heq
    have hroot : rootReflection index = 1 :=
      mul_right_cancel (heq.trans (one_mul element).symm)
    exact rootReflection_ne_one index hroot
  · intro hlength
    apply CoxeterSystem.BruhatStep.bruhatLE
    exact ⟨rootReflection index, hreflection,
      by simp only [← mul_assoc, rootReflection_mul_self, one_mul], hlength⟩

/-- Right reflection multiplication descends in Bruhat order exactly when length decreases. -/
theorem rootReflection_bruhatLE_mul_right_iff (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) (element : DihedralGroup n) :
    BruhatLE n hthree (element * rootReflection index) element ↔
      length n hthree (element * rootReflection index) < length n hthree element := by
  calc
    _ ↔ BruhatLE n hthree (element * rootReflection index)⁻¹ element⁻¹ :=
      (coxeterSystem n hthree).bruhatLE_inv_iff.symm
    _ ↔ length n hthree (element * rootReflection index)⁻¹ < length n hthree element⁻¹ := by
      rw [mul_inv_rev, (rootReflection_isReflection n hthree index).inv]
      exact rootReflection_bruhatLE_mul_left_iff n hthree index element⁻¹
    _ ↔ _ := by rw [length_inv, length_inv]

end Schubert.Dihedral
