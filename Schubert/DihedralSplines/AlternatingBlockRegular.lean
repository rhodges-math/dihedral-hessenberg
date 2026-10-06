import Schubert.DihedralSplines.AlternatingBlockEdges
import Mathlib.Data.Finset.Card

/-! # Regularity and boundary counts of alternating blocks -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem translated_prefix_injective (simple : Fin 2) (half : ℕ)
    (endpoint : PositiveRootIndex n) (hvalue : endpoint.val = 2 * half + simple.val)
    (vertex : DihedralGroup n) (first second : ℕ)
    (hfirst : first < 2 * half + 2) (hsecond : second < 2 * half + 2)
    (heq : vertex * alternatingPrefixProduct n hthree simple first =
      vertex * alternatingPrefixProduct n hthree simple second) : first = second := by
  have hbound := endpoint.isLt
  have hlength := congrArg (Schubert.Dihedral.length n hthree) (mul_left_cancel heq)
  rw [length_alternatingPrefixProduct n hthree simple first (by omega),
    length_alternatingPrefixProduct n hthree simple second (by omega)] at hlength
  exact hlength

/-- The alternating block has exactly twice its bipartite half-size many vertices. -/
theorem card_alternating_block (simple : Fin 2) (half : ℕ)
    (endpoint : PositiveRootIndex n) (hvalue : endpoint.val = 2 * half + simple.val)
    (vertex : DihedralGroup n) :
    ((Finset.range (2 * half + 2)).image
      (fun position => vertex * alternatingPrefixProduct n hthree simple position)).card =
        2 * half + 2 := by
  classical
  rw [Finset.card_image_iff.mpr, Finset.card_range]
  intro first hf second hs heq
  exact translated_prefix_injective simple half endpoint hvalue vertex first second
    (Finset.mem_range.mp hf) (Finset.mem_range.mp hs) heq

private theorem card_opposite_parity_positions (half position : ℕ) :
    ((Finset.range (2 * half + 2)).filter
      (fun second => position % 2 ≠ second % 2)).card = half + 1 := by
  classical
  let parity : ℕ := if position % 2 = 0 then 1 else 0
  have hparity : parity ≤ 1 ∧ parity % 2 ≠ position % 2 := by
    dsimp only [parity]
    split_ifs <;> omega
  symm
  rw [← Finset.card_range (half + 1)]
  apply Finset.card_bij (fun first _ => 2 * first + parity)
  · intro first hfirst
    simp only [Finset.mem_filter, Finset.mem_range]
    have := Finset.mem_range.mp hfirst
    omega
  · intro first hf second hs heq
    omega
  · intro second hsecond
    obtain ⟨hbound, hmod⟩ := Finset.mem_filter.mp hsecond
    have hsmall := Finset.mem_range.mp hbound
    refine ⟨second / 2, Finset.mem_range.mpr (by omega), ?_⟩
    omega

/-- Every vertex in an endpoint-selected block has the same number of internal root edges. -/
theorem card_internal_roots_alternating_block (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (vertex : DihedralGroup n) (position : ℕ) (hposition : position < 2 * half + 2) :
    let block := (Finset.range (2 * half + 2)).image
      (fun second => vertex * alternatingPrefixProduct n hthree simple second)
    (ideal.roots.filter (fun index =>
      (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index
        ∈ block)).card = half + 1 := by
  classical
  let block := (Finset.range (2 * half + 2)).image
    (fun second => vertex * alternatingPrefixProduct n hthree simple second)
  let internal := ideal.roots.filter (fun index =>
    (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index ∈ block)
  have hneighbor (index : PositiveRootIndex n) (hindex : index ∈ internal) :
      ∃ second ∈ Finset.range (2 * half + 2),
        vertex * alternatingPrefixProduct n hthree simple second =
          (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index :=
    Finset.mem_image.mp (Finset.mem_filter.mp hindex).2
  let neighbor (index : PositiveRootIndex n) (hindex : index ∈ internal) : ℕ :=
    (hneighbor index hindex).choose
  have hspec (index : PositiveRootIndex n) (hindex : index ∈ internal) :
      neighbor index hindex < 2 * half + 2 ∧
        vertex * alternatingPrefixProduct n hthree simple (neighbor index hindex) =
          (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index := by
    exact ⟨Finset.mem_range.mp (hneighbor index hindex).choose_spec.1,
      (hneighbor index hindex).choose_spec.2⟩
  change internal.card = half + 1
  rw [← card_opposite_parity_positions half position]
  apply Finset.card_bij neighbor
  · intro index hindex
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (hspec index hindex).1, ?_⟩
    apply (ideal.alternating_block_edge_iff_parity_ne simple half endpoint hvalue hendpoint
      vertex position (neighbor index hindex) (by omega)
        (by have := (hspec index hindex).1; omega)).mp
    exact ⟨index, (Finset.mem_filter.mp hindex).1, (hspec index hindex).2⟩
  · intro first hf second hs heq
    apply rootReflection_injective n
    apply mul_left_cancel (a := vertex * alternatingPrefixProduct n hthree simple position)
    rw [← (hspec first hf).2, ← (hspec second hs).2, heq]
  · intro second hsecond
    obtain ⟨hbound, hparity⟩ := Finset.mem_filter.mp hsecond
    have hsmall := Finset.mem_range.mp hbound
    obtain ⟨index, hmem, hedge⟩ :=
      (ideal.alternating_block_edge_iff_parity_ne simple half endpoint hvalue hendpoint
        vertex position second (by omega) (by omega)).mpr hparity
    have hindex : index ∈ internal := by
      apply Finset.mem_filter.mpr
      refine ⟨hmem, ?_⟩
      exact Finset.mem_image.mpr ⟨second, hbound, hedge⟩
    refine ⟨index, hindex, ?_⟩
    apply translated_prefix_injective simple half endpoint hvalue vertex _ _
      (hspec index hindex).1 hsmall
    exact (hspec index hindex).2.trans hedge.symm

/-- Every vertex of an alternating block has the same number of outgoing root edges. -/
theorem card_boundary_roots_alternating_block (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (vertex : DihedralGroup n) (position : ℕ) (hposition : position < 2 * half + 2) :
    let block := (Finset.range (2 * half + 2)).image
      (fun second => vertex * alternatingPrefixProduct n hthree simple second)
    (ideal.roots.filter (fun index =>
      (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index
        ∉ block)).card = ideal.roots.card - (half + 1) := by
  classical
  let block := (Finset.range (2 * half + 2)).image
    (fun second => vertex * alternatingPrefixProduct n hthree simple second)
  have hinternal := ideal.card_internal_roots_alternating_block simple half endpoint hvalue
    hendpoint vertex position hposition
  have hpartition := Finset.card_filter_add_card_filter_not (s := ideal.roots)
    (fun index =>
      (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index ∈ block)
  change (ideal.roots.filter (fun index =>
    (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index
      ∈ block)).card
      = half + 1 at hinternal
  change (ideal.roots.filter (fun index =>
    (vertex * alternatingPrefixProduct n hthree simple position) * rootReflection index
      ∉ block)).card
      = ideal.roots.card - (half + 1)
  omega

/-- Internal-edge invariance on the finite block forces a function to be constant. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.AlternatingBlock.eq_of_internal_edges (ideal
  : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (vertex : DihedralGroup n) {A : Sort*} (f : DihedralGroup n → A) :
    let block := (Finset.range (2 * half + 2)).image
      (fun position => vertex * alternatingPrefixProduct n hthree simple position)
    (∀ source ∈ block, ∀ index ∈ ideal.roots, source * rootReflection index ∈ block →
      f source = f (source * rootReflection index)) →
        ∀ target ∈ block, f target = f vertex := by
  classical
  dsimp only
  intro hedges target htarget
  obtain ⟨position, hposition, rfl⟩ := Finset.mem_image.mp htarget
  apply ideal.eq_on_alternating_block_of_eq_on_edges simple half endpoint hvalue hendpoint vertex f
    _ position (by have := Finset.mem_range.mp hposition; omega)
  intro first hfirst second hsecond index hindex heq
  rw [heq]
  apply hedges
  · exact Finset.mem_image.mpr ⟨first, Finset.mem_range.mpr (by omega), rfl⟩
  · exact hindex
  · exact Finset.mem_image.mpr ⟨second, Finset.mem_range.mpr (by omega), heq⟩

end Schubert.DihedralSplines.HessenbergSpace
