import Schubert.Dihedral.CyclicIntervals

/-! # The exact window of blocks meeting two adjacent source vertices -/

namespace Schubert.Dihedral.Cyclic

/-- Intervals meeting position zero or one have precisely the starts in the short tail window. -/
theorem source_window {n : ℕ} {hthree : 3 ≤ n} (size : ℕ)
    (hpositive : 0 < size) (hsize : size ≤ n) (start : Fin (2 * n)) :
    (vertex n hthree ⟨0, by omega⟩ ∈ interval n hthree start size ∨
      vertex n hthree ⟨1, by omega⟩ ∈ interval n hthree start size) ↔
      start.val ≤ 1 ∨ 2 * n - size + 1 ≤ start.val := by
  let : NeZero (2 * n) := ⟨by omega⟩
  rw [mem_interval _ _ _ (by omega), mem_interval _ _ _ (by omega)]
  fin_omega

end Schubert.Dihedral.Cyclic
