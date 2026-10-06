import Schubert.DihedralSplines.RootLayerOrder
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Parity

/-! # Classification of finite Hessenberg root ideals

The existing real root order forces every layer below an occupied layer to be
complete. Consequently an ideal is an initial segment, or an initial segment
with the last root replaced by the other root of that layer.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem natFinset_layer_classification (roots : Finset ℕ) (hone : 1 ∈ roots)
    (hlower : ∀ first second : ℕ, first / 2 < second / 2 → second ∈ roots → first ∈ roots) :
    roots = Finset.range roots.card ∨
      (Odd roots.card ∧ roots = insert roots.card (Finset.range (roots.card - 1))) := by
  let top := roots.max' ⟨1, hone⟩
  have htop : top ∈ roots := roots.max'_mem _
  have hbound : ∀ value ∈ roots, value ≤ top := fun value hmem => roots.le_max' value hmem
  have htopOne : 1 ≤ top := hbound 1 hone
  by_cases heven : top % 2 = 0
  · have hroots : roots = Finset.range (top + 1) := by
      ext value
      simp only [Finset.mem_range]
      constructor
      · intro hmem
        have := hbound value hmem
        omega
      · intro hlt
        by_cases heq : value = top
        · simpa only [heq] using htop
        · exact hlower value top (by omega) htop
    have hcard : roots.card = top + 1 := by rw [hroots, Finset.card_range]
    exact Or.inl (by rw [hcard]; exact hroots)
  · by_cases hcompanion : top - 1 ∈ roots
    · have hroots : roots = Finset.range (top + 1) := by
        ext value
        simp only [Finset.mem_range]
        constructor
        · intro hmem
          have := hbound value hmem
          omega
        · intro hlt
          by_cases heq : value = top
          · simpa only [heq] using htop
          · by_cases hother : value = top - 1
            · simpa only [hother] using hcompanion
            · exact hlower value top (by omega) htop
      have hcard : roots.card = top + 1 := by rw [hroots, Finset.card_range]
      exact Or.inl (by rw [hcard]; exact hroots)
    · have hroots : roots = insert top (Finset.range (top - 1)) := by
        ext value
        simp only [Finset.mem_insert, Finset.mem_range]
        constructor
        · intro hmem
          have hle := hbound value hmem
          by_cases heq : value = top
          · exact Or.inl heq
          · have hne : value ≠ top - 1 := by
              intro hother
              apply hcompanion
              simpa only [hother] using hmem
            exact Or.inr (by omega)
        · rintro (rfl | hlt)
          · exact htop
          · exact hlower value top (by omega) htop
      have hnot : top ∉ Finset.range (top - 1) := by simp only [Finset.mem_range]; omega
      have hcard : roots.card = top := by
        rw [hroots, Finset.card_insert_of_notMem hnot, Finset.card_range]
        omega
      apply Or.inr
      constructor
      · rw [hcard, Nat.odd_iff]
        omega
      · rw [hcard]
        exact hroots

namespace HessenbergSpace

/-- A Hessenberg ideal is an initial segment or has the other root of its final layer. -/
theorem root_membership_classification {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) :
    (∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔ index.val < ideal.roots.card) ∨
      (Odd ideal.roots.card ∧ ideal.roots.card < n ∧
        ∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔
          index.val < ideal.roots.card - 1 ∨ index.val = ideal.roots.card) := by
  classical
  let values := ideal.roots.image Fin.val
  have hcard : values.card = ideal.roots.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have hone : 1 ∈ values := by
    apply Finset.mem_image.mpr
    refine ⟨secondSimpleRootIndex n hthree, ideal.second_mem, ?_⟩
    simp only [secondSimpleRootIndex, Fin.val_mk]
  have hmem (index : PositiveRootIndex n) : index ∈ ideal.roots ↔ index.val ∈ values := by
    constructor
    · intro hindex
      exact Finset.mem_image.mpr ⟨index, hindex, rfl⟩
    · intro hvalue
      obtain ⟨other, hother, heq⟩ := Finset.mem_image.mp hvalue
      have heqIndex : other = index := Fin.ext heq
      simpa only [heqIndex] using hother
  have hlower : ∀ first second : ℕ, first / 2 < second / 2 →
      second ∈ values → first ∈ values := by
    intro first second hlt hsecond
    obtain ⟨larger, hlarger, heq⟩ := Finset.mem_image.mp hsecond
    have hfirstBound : first < n := by have := larger.isLt; omega
    let smaller : PositiveRootIndex n := ⟨first, hfirstBound⟩
    have hrootLE : RootLE n hthree smaller larger :=
      (rootLE_iff_eq_or_layer_lt n hthree smaller larger).mpr (Or.inr (by
        simp only [smaller]
        omega))
    exact Finset.mem_image.mpr ⟨smaller, ideal.lower hrootLE hlarger, rfl⟩
  rcases natFinset_layer_classification values hone hlower with hprefix | ⟨hodd, hother⟩
  · apply Or.inl
    intro index
    rw [hmem, hprefix, Finset.mem_range, hcard]
  · apply Or.inr
    have htop : values.card ∈ values := Eq.mpr
      (congrArg (fun rootSet : Finset ℕ => values.card ∈ rootSet) hother)
      (Finset.mem_insert_self values.card (Finset.range (values.card - 1)))
    obtain ⟨top, _, htopValue⟩ := Finset.mem_image.mp htop
    refine ⟨by simpa only [hcard] using hodd, ?_, ?_⟩
    · rw [← hcard, ← htopValue]
      exact top.isLt
    · intro index
      rw [hmem, hother]
      simp only [Finset.mem_insert, Finset.mem_range, hcard, or_comm]


/-- Every Hessenberg ideal has one of the two paper forms with the stated parameter bounds. -/
theorem paper_family_classification {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergSpace n hthree) :
    (∃ size : ℕ, 2 ≤ size ∧ size ≤ n ∧
      ∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔ index.val < size) ∨
    (∃ layer : ℕ, 2 ≤ layer ∧ layer ≤ n / 2 ∧
      ∀ index : PositiveRootIndex n, index ∈ ideal.roots ↔
        index.val < 2 * layer - 2 ∨ index.val = 2 * layer - 1) := by
  have hminimum := ideal.two_le_card
  rcases ideal.root_membership_classification with hprefix | ⟨hodd, hbound, hother⟩
  · exact Or.inl ⟨ideal.roots.card, hminimum, ideal.card_le, hprefix⟩
  · let layer := (ideal.roots.card + 1) / 2
    have hparity := Nat.odd_iff.mp hodd
    have hlast : 2 * layer - 1 = ideal.roots.card := by dsimp [layer]; omega
    have hprevious : 2 * layer - 2 = ideal.roots.card - 1 := by dsimp [layer]; omega
    apply Or.inr
    refine ⟨layer, by dsimp [layer]; omega, by dsimp [layer]; omega, ?_⟩
    intro index
    rw [hlast, hprevious]
    exact hother index

end HessenbergSpace

end Schubert.DihedralSplines
