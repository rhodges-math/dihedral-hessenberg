import DihedralHessenberg.Paper.RootLayerOrder

/-! # The two families of Hessenberg root ideals

Every permitted initial segment and every permitted choice of the other root in
its final layer is an ideal for the real simple-root cone order.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

/-- Every initial segment containing both simple roots is a Hessenberg ideal. -/
theorem exists_initial_segment (n : ℕ) (hthree : 3 ≤ n) (size : ℕ)
    (htwo : 2 ≤ size) (hbound : size ≤ n) :
    ∃ ideal : HessenbergSpace n hthree, ideal.roots.card = size ∧
      ∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔ index.val < size := by
  classical
  let lift : Fin size → PositiveRootIndex n := fun index =>
    ⟨index.val, index.isLt.trans_le hbound⟩
  let rootSet := Finset.univ.image lift
  have hlift : Function.Injective lift := by
    intro first second heq
    exact Fin.ext (congrArg (fun index : PositiveRootIndex n => index.val) heq)
  have hmem (index : PositiveRootIndex n) : index ∈ rootSet ↔ index.val < size := by
    constructor
    · intro hindex
      obtain ⟨smaller, _, heq⟩ := Finset.mem_image.mp hindex
      rw [← heq]
      exact smaller.isLt
    · intro hlt
      exact Finset.mem_image.mpr ⟨⟨index.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  have hcard : rootSet.card = size := by
    rw [Finset.card_image_of_injective _ hlift, Finset.card_univ, Fintype.card_fin]
  let ideal : HessenbergSpace n hthree := {
    roots := rootSet
    lower := by
      intro first second hle hsecond
      apply (hmem first).mpr
      have hsecondBound := (hmem second).mp hsecond
      rcases (rootLE_iff_eq_or_layer_lt n hthree first second).mp hle with heq | hlt
      · simpa only [heq] using hsecondBound
      · omega
    first_mem := by
      apply (hmem _).mpr
      simp only [firstSimpleRootIndex, Fin.val_mk]
      omega
    second_mem := by
      apply (hmem _).mpr
      simp only [secondSimpleRootIndex, Fin.val_mk]
      omega }
  exact ⟨ideal, hcard, hmem⟩

/-- Choosing the other root of a final pair also gives a Hessenberg ideal. -/
theorem exists_other_root_final_layer (n : ℕ) (hthree : 3 ≤ n) (layer : ℕ)
    (htwo : 2 ≤ layer) (hbound : layer ≤ n / 2) :
    ∃ ideal : HessenbergSpace n hthree, ideal.roots.card = 2 * layer - 1 ∧
      ∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔
        index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1 := by
  classical
  obtain ⟨initialIdeal, hcard, hprefix⟩ := exists_initial_segment n hthree (2 * layer - 2)
    (by omega) (by omega)
  let extra : PositiveRootIndex n := ⟨2 * layer - 1, by omega⟩
  let rootSet := insert extra initialIdeal.roots
  have hextra : extra ∉ initialIdeal.roots := by
    rw [hprefix]
    simp only [extra]
    omega
  have hmem (index : PositiveRootIndex n) : index ∈ rootSet ↔
      index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1 := by
    change index ∈ insert extra initialIdeal.roots ↔ _
    rw [Finset.mem_insert, hprefix]
    have heq : index = extra ↔ index.val = 2 * layer - 1 := by
      constructor
      · intro hindex
        simpa only [extra, Fin.val_mk] using congrArg Fin.val hindex
      · intro hvalue
        exact Fin.ext hvalue
    rw [heq, or_comm]
  let ideal : HessenbergSpace n hthree := {
    roots := rootSet
    lower := by
      intro first second hle hsecond
      apply (hmem first).mpr
      rcases (rootLE_iff_eq_or_layer_lt n hthree first second).mp hle with heq | hlt
      · simpa only [heq] using (hmem second).mp hsecond
      · rcases (hmem second).mp hsecond with hprefixBound | hextraValue
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
    first_mem := Finset.mem_insert_of_mem initialIdeal.first_mem
    second_mem := Finset.mem_insert_of_mem initialIdeal.second_mem }
  refine ⟨ideal, ?_, hmem⟩
  change (insert extra initialIdeal.roots).card = 2 * layer - 1
  rw [Finset.card_insert_of_notMem hextra, hcard]
  omega

end Schubert.DihedralSplines.HessenbergSpace
