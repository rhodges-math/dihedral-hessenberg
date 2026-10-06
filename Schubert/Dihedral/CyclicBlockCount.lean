import Schubert.Dihedral.CyclicBlockForms

/-! # Cardinality of distinct alternating blocks -/

noncomputable section

namespace Schubert.Dihedral

/-- The two block orientations together describe exactly two n distinct vertex sets. -/
theorem card_alternating_blocks {n : ℕ} {hthree : 3 ≤ n} (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    Nat.card {block : Finset (DihedralGroup n) // ∃ element : DihedralGroup n,
      block = alternatingBlock element (simpleRoot n hthree 0) (simpleRoot n hthree 1) half ∨
      block = alternatingBlock element (simpleRoot n hthree 1) (simpleRoot n hthree 0) half} =
        2 * n := by
  classical
  let family := {block : Finset (DihedralGroup n) // ∃ element : DihedralGroup n,
    block = alternatingBlock element (simpleRoot n hthree 0) (simpleRoot n hthree 1) half ∨
    block = alternatingBlock element (simpleRoot n hthree 1) (simpleRoot n hthree 0) half}
  let function : Fin (2 * n) → family := fun start =>
    ⟨Cyclic.interval n hthree start (2 * half + 2), by
      refine ⟨Cyclic.vertex n hthree start, ?_⟩
      by_cases heven : Even start.val
      · exact Or.inl (Cyclic.interval_even start half heven)
      · exact Or.inr (Cyclic.interval_odd start half heven)⟩
  have hinjective : Function.Injective function := by
    intro first second heq
    exact Cyclic.interval_injective (2 * half + 2) (by omega) (by omega)
      (congrArg Subtype.val heq)
  have hsurjective : Function.Surjective function := by
    rintro ⟨block, element, hfirst | hsecond⟩
    · obtain ⟨start, _, hinterval⟩ := Cyclic.first_interval element half hbound
      refine ⟨start, Subtype.ext ?_⟩
      exact hinterval.symm.trans hfirst.symm
    · obtain ⟨start, _, hinterval⟩ := Cyclic.second_interval element half hbound
      refine ⟨start, Subtype.ext ?_⟩
      exact hinterval.symm.trans hsecond.symm
  let equivalence := Equiv.ofBijective function ⟨hinjective, hsurjective⟩
  exact (Nat.card_congr equivalence).symm.trans (Nat.card_fin (2 * n))

end Schubert.Dihedral
