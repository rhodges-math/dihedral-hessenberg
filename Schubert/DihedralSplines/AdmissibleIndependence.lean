import Schubert.DihedralSplines.BoundaryAugmentation
import Schubert.DihedralSplines.OddIdealExtension
import Schubert.DihedralSplines.BlockExcludedRoot
import Schubert.Dihedral.AlternatingWords

/-! # Independence on admissible blocks of proper odd Hessenberg ideals -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- Distinct block sets with a selected terminal reflection and fixed size. -/
abbrev AdmissibleBlocks {n : ℕ} {hthree : 3 ≤ n}
    (ideal : HessenbergIdeal n hthree) (half : ℕ) :=
  {vertices : Finset (DihedralGroup n) //
    ∃ block : Block ideal, block.half = half ∧ block.vertices = vertices}

/-- Admissible sets are exactly the two orientations
whose numbered terminal root is selected. -/
theorem admissible_iff {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (half : ℕ) (hbound : 2 * half + 1 < n) (vertices : Finset (DihedralGroup n)) :
    (∃ block : Block ideal, block.half = half ∧ block.vertices = vertices) ↔
      ((positiveRootEquiv n ⟨2 * half, by omega⟩).val ∈ ideal ∧
        ∃ base, vertices = alternatingBlock base (simpleRoot n hthree 0)
          (simpleRoot n hthree 1) half) ∨
      ((positiveRootEquiv n ⟨2 * half + 1, hbound⟩).val ∈ ideal ∧
        ∃ base, vertices = alternatingBlock base (simpleRoot n hthree 1)
          (simpleRoot n hthree 0) half) := by
  constructor
  · rintro ⟨block, hhalf, hvertices⟩
    rcases block.pair with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · have hreflection : (positiveRootEquiv n ⟨2 * half, by omega⟩).reflection =
          block.alpha.alternatingProduct block.beta (2 * block.half + 1) := by
        rw [hfirst, hsecond, hhalf, PositiveRoot.alternating_odd,
          simpleRoot_reflection, simpleRoot_reflection, simpleReflection_zero,
          simpleReflection_one]
        exact numbered_even_reflection n half (by omega)
      have heq := PositiveRoot.reflection_injective n (block.terminal.trans hreflection.symm)
      refine Or.inl ⟨heq ▸ block.selected, block.base, ?_⟩
      rw [← hvertices]
      simp only [Block.vertices, hfirst, hsecond, hhalf]
    · have hreflection : (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection =
          block.alpha.alternatingProduct block.beta (2 * block.half + 1) := by
        rw [hfirst, hsecond, hhalf, PositiveRoot.alternating_odd,
          simpleRoot_reflection, simpleRoot_reflection, simpleReflection_one,
          simpleReflection_zero]
        exact numbered_odd_reflection n half hbound
      have heq := PositiveRoot.reflection_injective n (block.terminal.trans hreflection.symm)
      refine Or.inr ⟨heq ▸ block.selected, block.base, ?_⟩
      rw [← hvertices]
      simp only [Block.vertices, hfirst, hsecond, hhalf]
  · rintro (⟨hselected, base, hvertices⟩ | ⟨hselected, base, hvertices⟩)
    · exact ⟨Block.first ideal base half (by omega) hselected, rfl, hvertices.symm⟩
    · exact ⟨Block.second ideal base half hbound hselected, rfl, hvertices.symm⟩
/-- Boundary functions on all admissible blocks of a proper odd ideal are independent. -/
theorem admissible_independent {n : ℕ} {hthree : 3 ≤ n} [NeZero n]
    (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (coefficient : AdmissibleBlocks ideal half → DihedralGroup n → ℂ)
    (hcoefficient : ∀ block vertex, vertex ∈ block.val → coefficient block vertex ≠ 0) :
    LinearIndependent ℂ (fun block : AdmissibleBlocks ideal half =>
      ideal.toRootSubset.boundaryFunction (block.val : Set (DihedralGroup n))
        (coefficient block)) := by
  classical
  let : Fintype (AdmissibleBlocks ideal half) := Fintype.ofFinite _
  have hbound : 2 * half + 1 < n := by
    have hlt := ideal.card_lt hproper
    omega
  obtain ⟨larger, delta, _, hmissing, hcarrier, hprefix⟩ :=
    ideal.odd_extension half hcard hproper
  have hshort : ∀ alpha : PositiveRoot n,
      Schubert.Dihedral.length n hthree alpha.reflection ≤ 2 * half + 1 →
        alpha.val ∈ larger.toRootSubset := by
    intro alpha hlength
    change alpha.val ∈ larger.carrier
    rw [hprefix]
    change Schubert.Dihedral.length n hthree (rootReflection alpha.index) ≤ _ at hlength
    rw [length_rootReflection] at hlength
    exact ⟨alpha.index, by change alpha.index.val < 2 * half + 2; omega, alpha.index_val⟩
  have hblocks : ∀ index : AdmissibleBlocks ideal half,
      (∃ base, index.val = alternatingBlock base (simpleRoot n hthree 0)
        (simpleRoot n hthree 1) half) ∨
      (∃ base, index.val = alternatingBlock base (simpleRoot n hthree 1)
        (simpleRoot n hthree 0) half) := by
    intro index
    obtain ⟨block, hhalf, hvertices⟩ := index.property
    rw [← hvertices]
    change (∃ base, alternatingBlock block.base block.alpha block.beta block.half =
      alternatingBlock base (simpleRoot n hthree 0) (simpleRoot n hthree 1) half) ∨ _
    rcases block.pair with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Or.inl ⟨block.base, by simp only [hfirst, hsecond, hhalf]⟩
    · exact Or.inr ⟨block.base, by simp only [Block.vertices, hfirst, hsecond, hhalf]⟩
  apply ideal.toRootSubset.independent_of_insert larger.toRootSubset delta hmissing hcarrier
    (fun block => (block.val : Set (DihedralGroup n))) coefficient
  · intro index vertex hvertex
    obtain ⟨block, _, hvertices⟩ := index.property
    rw [← hvertices] at hvertex ⊢
    exact block.excluded_leaves delta hmissing vertex hvertex
  · exact larger.toRootSubset.subfamily_independent half hbound hshort Subtype.val
      Subtype.val_injective hblocks coefficient hcoefficient

end Schubert.DihedralSplines.HessenbergIdeal
