import Schubert.DihedralSplines.BoundaryRelations
import Schubert.DihedralSplines.BlockSeparation
import Schubert.Dihedral.CyclicBlockCount

/-! # Independence of functions on distinct alternating blocks -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

/-- The distinct vertex sets of the two alternating block orientations. -/
abbrev AlternatingBlocks (n : ℕ) (hthree : 3 ≤ n) (half : ℕ) :=
  {block : Finset (DihedralGroup n) // ∃ base : DihedralGroup n,
    block = alternatingBlock base (simpleRoot n hthree 0) (simpleRoot n hthree 1) half ∨
    block = alternatingBlock base (simpleRoot n hthree 1) (simpleRoot n hthree 0) half}

/-- Short-reflection separation proves independence for arbitrary nonzero block coefficients. -/
theorem block_independent {n : ℕ} {hthree : 3 ≤ n} (selected : RootSubset n)
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      Schubert.Dihedral.length n hthree alpha.reflection ≤ 2 * half + 1 →
        alpha.val ∈ selected)
    (coefficient : AlternatingBlocks n hthree half → DihedralGroup n → ℂ)
    (hcoefficient : ∀ block vertex, vertex ∈ block.val → coefficient block vertex ≠ 0) :
    LinearIndependent ℂ (fun block : AlternatingBlocks n hthree half =>
      selected.boundaryFunction (block.val : Set (DihedralGroup n)) (coefficient block)) := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : Fintype (AlternatingBlocks n hthree half) := Fintype.ofFinite _
  apply selected.independent_of_separation _ coefficient hcoefficient
  intro active hactive
  obtain ⟨chosen, hchosen, source, hsource, hseparate⟩ :=
    selected.block_separation half hbound hselected (Subtype.val '' active)
      (Set.Nonempty.image _ hactive) (by
        rintro block ⟨index, _, rfl⟩
        obtain ⟨base, hfirst | hsecond⟩ := index.property
        · exact Or.inl ⟨base, hfirst⟩
        · exact Or.inr ⟨base, hsecond⟩)
  obtain ⟨index, hindex, rfl⟩ := hchosen
  refine ⟨index, hindex, source, hsource, ?_⟩
  rcases hseparate with hterminal | ⟨alpha, halpha, htarget, hother⟩
  · left
    intro other hactiveOther hne
    exact hterminal other.val ⟨other, hactiveOther, rfl⟩
      (fun heq => hne (Subtype.ext heq))
  · right
    refine ⟨alpha, halpha, htarget, ?_⟩
    intro other hactiveOther hne hsourceOther
    exact hother other.val ⟨other, hactiveOther, rfl⟩
      (fun heq => hne (Subtype.ext heq)) hsourceOther

/-- For exactly the short-reflection root set, the displayed block functions are independent. -/
theorem independent {n : ℕ} {hthree : 3 ≤ n} (selected : RootSubset n)
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n, alpha.val ∈ selected ↔
      Schubert.Dihedral.length n hthree alpha.reflection ≤ 2 * half + 1)
    (coefficient : AlternatingBlocks n hthree half → DihedralGroup n → ℂ)
    (hcoefficient : ∀ block vertex, vertex ∈ block.val → coefficient block vertex ≠ 0) :
    LinearIndependent ℂ (fun block : AlternatingBlocks n hthree half =>
      selected.boundaryFunction (block.val : Set (DihedralGroup n)) (coefficient block)) :=
  selected.block_independent half hbound (fun alpha => (hselected alpha).mpr)
    coefficient hcoefficient

/-- Any injectively indexed subfamily of short alternating blocks has independent functions. -/
theorem subfamily_independent {n : ℕ} {hthree : 3 ≤ n} {I : Type*} [Fintype I]
    (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      Schubert.Dihedral.length n hthree alpha.reflection ≤ 2 * half + 1 →
        alpha.val ∈ selected)
    (vertices : I → Finset (DihedralGroup n)) (hinjective : Function.Injective vertices)
    (hblocks : ∀ index, (∃ base, vertices index =
      alternatingBlock base (simpleRoot n hthree 0) (simpleRoot n hthree 1) half) ∨
      (∃ base, vertices index =
        alternatingBlock base (simpleRoot n hthree 1) (simpleRoot n hthree 0) half))
    (coefficient : I → DihedralGroup n → ℂ)
    (hcoefficient : ∀ index vertex, vertex ∈ vertices index → coefficient index vertex ≠ 0) :
    LinearIndependent ℂ (fun index => selected.boundaryFunction
      (vertices index : Set (DihedralGroup n)) (coefficient index)) := by
  classical
  let : NeZero n := ⟨by omega⟩
  apply selected.independent_of_separation _ coefficient hcoefficient
  intro active hactive
  obtain ⟨chosen, hchosen, source, hsource, hseparate⟩ :=
    selected.block_separation half hbound hselected (vertices '' active)
      (Set.Nonempty.image _ hactive) (by
        rintro block ⟨index, _, rfl⟩
        exact hblocks index)
  obtain ⟨index, hindex, rfl⟩ := hchosen
  refine ⟨index, hindex, source, hsource, ?_⟩
  rcases hseparate with hterminal | ⟨alpha, halpha, htarget, hother⟩
  · left
    intro other hactiveOther hne
    exact hterminal (vertices other) ⟨other, hactiveOther, rfl⟩
      (fun heq => hne (hinjective heq))
  · right
    refine ⟨alpha, halpha, htarget, ?_⟩
    intro other hactiveOther hne hsourceOther
    exact hother (vertices other) ⟨other, hactiveOther, rfl⟩
      (fun heq => hne (hinjective heq)) hsourceOther
end Schubert.Dihedral.RootSubset
