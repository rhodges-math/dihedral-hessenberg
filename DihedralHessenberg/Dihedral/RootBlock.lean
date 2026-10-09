import DihedralHessenberg.Dihedral.RootAlternatingProduct
import Mathlib.Data.Finset.Image

/-! # Finite alternating blocks of root reflections -/

noncomputable section

namespace Schubert.Dihedral

/-- A translated block of consecutive prefixes of an alternating reflection word. -/
def alternatingBlock {n : ℕ} (vertex : DihedralGroup n) (alpha beta : PositiveRoot n)
    (half : ℕ) : Finset (DihedralGroup n) := by
  classical
  exact (Finset.range (2 * half + 2)).image
    (fun position => vertex * alpha.alternatingProduct beta position)

/-- Block membership is an exact bounded alternating-prefix expression. -/
theorem mem_alternatingBlock {n : ℕ} (vertex target : DihedralGroup n)
    (alpha beta : PositiveRoot n) (half : ℕ) :
    target ∈ alternatingBlock vertex alpha beta half ↔
      ∃ position < 2 * half + 2,
        vertex * alpha.alternatingProduct beta position = target := by
  classical
  simp only [alternatingBlock, Finset.mem_image, Finset.mem_range]

/-- Every alternating block contains its translating vertex. -/
theorem vertex_mem_alternatingBlock {n : ℕ} (vertex : DihedralGroup n)
    (alpha beta : PositiveRoot n) (half : ℕ) :
    vertex ∈ alternatingBlock vertex alpha beta half := by
  apply (mem_alternatingBlock vertex vertex alpha beta half).mpr
  exact ⟨0, by omega, by rw [PositiveRoot.alternating_zero, mul_one]⟩

end Schubert.Dihedral
