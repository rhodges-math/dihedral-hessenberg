import Schubert.Dihedral.AlternatingPrefixes
import Schubert.DihedralSplines.RootLayerOrder

/-! # Internal reflection edges of alternating blocks -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem root_mem_below_endpoint (ideal : HessenbergSpace n hthree)
    (endpoint index : PositiveRootIndex n) (hendpoint : endpoint ∈ ideal.roots)
    (hposition : index = endpoint ∨ index.val / 2 < endpoint.val / 2) :
    index ∈ ideal.roots :=
  ideal.lower ((rootLE_iff_eq_or_layer_lt n hthree index endpoint).mpr hposition) hendpoint

/-- Every even prefix and every odd prefix of an endpoint-selected block are adjacent. -/
theorem alternating_block_even_odd_edge (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (first second : ℕ) (hfirst : first ≤ half) (hsecond : second ≤ half) :
    ∃ index ∈ ideal.roots,
      alternatingPrefixProduct n hthree simple (2 * second + 1) =
        alternatingPrefixProduct n hthree simple (2 * first) * rootReflection index := by
  have hbound := endpoint.isLt
  fin_cases simple
  · have hend : endpoint.val = 2 * half := hvalue
    change ∃ index ∈ ideal.roots,
      alternatingPrefixProduct n hthree 0 (2 * second + 1) =
        alternatingPrefixProduct n hthree 0 (2 * first) * rootReflection index
    by_cases hle : first ≤ second
    · let index : PositiveRootIndex n := ⟨2 * (second - first), by omega⟩
      have hmem : index ∈ ideal.roots := by
        apply root_mem_below_endpoint ideal endpoint index hendpoint
        by_cases hequal : second - first = half
        · left
          apply Fin.ext
          simp only [index]
          omega
        · right
          dsimp only [index]
          omega
      refine ⟨index, hmem, ?_⟩
      rw [alternatingPrefixProduct_zero_even, alternatingPrefixProduct_zero_odd,
        rootReflection_eq_sr_of_even index (by dsimp [index]; omega)]
      have hquot : index.val / 2 = second - first := by dsimp [index]; omega
      rw [hquot, DihedralGroup.r_mul_sr, Nat.cast_sub hle]
      congr 1
      ring
    · let index : PositiveRootIndex n := ⟨2 * (first - second) - 1, by omega⟩
      have hmem : index ∈ ideal.roots := by
        apply root_mem_below_endpoint ideal endpoint index hendpoint
        right
        dsimp only [index]
        omega
      refine ⟨index, hmem, ?_⟩
      rw [alternatingPrefixProduct_zero_even, alternatingPrefixProduct_zero_odd,
        rootReflection_eq_sr_of_odd index (by dsimp [index]; omega)]
      have hquot : index.val / 2 = first - second - 1 := by dsimp [index]; omega
      rw [hquot, DihedralGroup.r_mul_sr,
        Nat.cast_sub (show 1 ≤ first - second by omega), Nat.cast_sub (by omega)]
      congr 1
      ring
  · have hend : endpoint.val = 2 * half + 1 := hvalue
    change ∃ index ∈ ideal.roots,
      alternatingPrefixProduct n hthree 1 (2 * second + 1) =
        alternatingPrefixProduct n hthree 1 (2 * first) * rootReflection index
    by_cases hle : first ≤ second
    · let index : PositiveRootIndex n := ⟨2 * (second - first) + 1, by omega⟩
      have hmem : index ∈ ideal.roots := by
        apply root_mem_below_endpoint ideal endpoint index hendpoint
        by_cases hequal : second - first = half
        · left
          apply Fin.ext
          simp only [index]
          omega
        · right
          dsimp only [index]
          omega
      refine ⟨index, hmem, ?_⟩
      rw [alternatingPrefixProduct_one_even, alternatingPrefixProduct_one_odd,
        rootReflection_eq_sr_of_odd index (by dsimp [index]; omega)]
      have hquot : index.val / 2 = second - first := by dsimp [index]; omega
      rw [hquot, DihedralGroup.r_mul_sr, Nat.cast_sub hle]
      congr 1
      ring
    · let index : PositiveRootIndex n := ⟨2 * (first - second - 1), by omega⟩
      have hmem : index ∈ ideal.roots := by
        apply root_mem_below_endpoint ideal endpoint index hendpoint
        right
        dsimp only [index]
        omega
      refine ⟨index, hmem, ?_⟩
      rw [alternatingPrefixProduct_one_even, alternatingPrefixProduct_one_odd,
        rootReflection_eq_sr_of_even index (by dsimp [index]; omega)]
      have hquot : index.val / 2 = first - second - 1 := by dsimp [index]; omega
      rw [hquot, DihedralGroup.r_mul_sr,
        Nat.cast_sub (show 1 ≤ first - second by omega), Nat.cast_sub (by omega)]
      congr 1
      ring

private theorem even_prefix_not_even_edge (simple : Fin 2) (first second : ℕ)
    (index : PositiveRootIndex n) :
    alternatingPrefixProduct n hthree simple (2 * second) ≠
      alternatingPrefixProduct n hthree simple (2 * first) * rootReflection index := by
  fin_cases simple
  · change alternatingPrefixProduct n hthree 0 (2 * second) ≠
      alternatingPrefixProduct n hthree 0 (2 * first) * rootReflection index
    rw [alternatingPrefixProduct_zero_even, alternatingPrefixProduct_zero_even,
      rootReflection_eq_sr, DihedralGroup.r_mul_sr]
    intro heq
    cases heq
  · change alternatingPrefixProduct n hthree 1 (2 * second) ≠
      alternatingPrefixProduct n hthree 1 (2 * first) * rootReflection index
    rw [alternatingPrefixProduct_one_even, alternatingPrefixProduct_one_even,
      rootReflection_eq_sr, DihedralGroup.r_mul_sr]
    intro heq
    cases heq

private theorem odd_prefix_not_odd_edge (simple : Fin 2) (first second : ℕ)
    (index : PositiveRootIndex n) :
    alternatingPrefixProduct n hthree simple (2 * second + 1) ≠
      alternatingPrefixProduct n hthree simple (2 * first + 1) * rootReflection index := by
  fin_cases simple
  · change alternatingPrefixProduct n hthree 0 (2 * second + 1) ≠
      alternatingPrefixProduct n hthree 0 (2 * first + 1) * rootReflection index
    rw [alternatingPrefixProduct_zero_odd, alternatingPrefixProduct_zero_odd,
      rootReflection_eq_sr, DihedralGroup.sr_mul_sr]
    intro heq
    cases heq
  · change alternatingPrefixProduct n hthree 1 (2 * second + 1) ≠
      alternatingPrefixProduct n hthree 1 (2 * first + 1) * rootReflection index
    rw [alternatingPrefixProduct_one_odd, alternatingPrefixProduct_one_odd,
      rootReflection_eq_sr, DihedralGroup.sr_mul_sr]
    intro heq
    cases heq

/-- The graph on the translated alternating block is exactly the complete bipartite graph. -/
theorem alternating_block_edge_iff_parity_ne (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (vertex : DihedralGroup n) (first second : ℕ)
    (hfirst : first ≤ 2 * half + 1) (hsecond : second ≤ 2 * half + 1) :
    (∃ index ∈ ideal.roots,
      vertex * alternatingPrefixProduct n hthree simple second =
        (vertex * alternatingPrefixProduct n hthree simple first) * rootReflection index) ↔
      first % 2 ≠ second % 2 := by
  have heven (size : ℕ) (he : size % 2 = 0) : size = 2 * (size / 2) := by omega
  have hodd (size : ℕ) (he : size % 2 ≠ 0) : size = 2 * (size / 2) + 1 := by omega
  by_cases hf : first % 2 = 0
  · by_cases hs : second % 2 = 0
    · constructor
      · rintro ⟨index, _, hedge⟩
        have heq := mul_left_cancel (by simpa only [mul_assoc] using hedge)
        rw [heven first hf, heven second hs] at heq
        exact (even_prefix_not_even_edge simple (first / 2) (second / 2) index heq).elim
      · simp only [hf, hs, ne_eq, not_true_eq_false, false_implies]
    · constructor
      · intro _
        omega
      · intro _
        obtain ⟨index, hmem, heq⟩ := ideal.alternating_block_even_odd_edge simple half endpoint
          hvalue hendpoint (first / 2) (second / 2) (by omega) (by omega)
        refine ⟨index, hmem, ?_⟩
        rw [heven first hf, hodd second hs, heq, mul_assoc]
  · by_cases hs : second % 2 = 0
    · constructor
      · intro _
        omega
      · intro _
        obtain ⟨index, hmem, heq⟩ := ideal.alternating_block_even_odd_edge simple half endpoint
          hvalue hendpoint (second / 2) (first / 2) (by omega) (by omega)
        refine ⟨index, hmem, ?_⟩
        rw [hodd first hf, heven second hs, heq, mul_assoc, mul_assoc,
          rootReflection_mul_self, mul_one]
    · constructor
      · rintro ⟨index, _, hedge⟩
        have heq := mul_left_cancel (by simpa only [mul_assoc] using hedge)
        rw [hodd first hf, hodd second hs] at heq
        exact (odd_prefix_not_odd_edge simple (first / 2) (second / 2) index heq).elim
      · have hsame : first % 2 = second % 2 := by omega
        simp only [hsame, ne_eq, not_true_eq_false, false_implies]

/-- A function constant along internal edges is constant on an alternating block. -/
theorem eq_on_alternating_block_of_eq_on_edges (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (half : ℕ) (endpoint : PositiveRootIndex n)
    (hvalue : endpoint.val = 2 * half + simple.val) (hendpoint : endpoint ∈ ideal.roots)
    (vertex : DihedralGroup n) {A : Sort*} (f : DihedralGroup n → A)
    (hedges : ∀ first ≤ 2 * half + 1, ∀ second ≤ 2 * half + 1,
      ∀ index ∈ ideal.roots,
        vertex * alternatingPrefixProduct n hthree simple second =
          (vertex * alternatingPrefixProduct n hthree simple first) * rootReflection index →
        f (vertex * alternatingPrefixProduct n hthree simple first) =
          f (vertex * alternatingPrefixProduct n hthree simple second))
    (position : ℕ) (hposition : position ≤ 2 * half + 1) :
    f (vertex * alternatingPrefixProduct n hthree simple position) = f vertex := by
  have hstep (first second : ℕ) (hf : first ≤ 2 * half + 1)
      (hs : second ≤ 2 * half + 1) (hparity : first % 2 ≠ second % 2) :
      f (vertex * alternatingPrefixProduct n hthree simple first) =
        f (vertex * alternatingPrefixProduct n hthree simple second) := by
    obtain ⟨index, hmem, heq⟩ :=
      (ideal.alternating_block_edge_iff_parity_ne simple half endpoint hvalue hendpoint
        vertex first second hf hs).mpr hparity
    exact hedges first hf second hs index hmem heq
  have hzero : alternatingPrefixProduct n hthree simple 0 = 1 := by
    simp [alternatingPrefixProduct, CoxeterSystem.alternatingWord]
  have hresult : f (vertex * alternatingPrefixProduct n hthree simple position) =
      f (vertex * alternatingPrefixProduct n hthree simple 0) := by
    by_cases heven : position % 2 = 0
    · exact (hstep position 1 hposition (by omega) (by omega)).trans
        (hstep 0 1 (by omega) (by omega) (by decide)).symm
    · exact hstep position 0 hposition (by omega) (by omega)
  simpa only [hzero, mul_one] using hresult

end Schubert.DihedralSplines.HessenbergSpace
