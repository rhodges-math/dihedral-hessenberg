import Schubert.Dihedral.AlternatingAppend
import Schubert.Dihedral.RootBlock

/-! # Reversal of alternating vertex blocks -/

namespace Schubert.Dihedral.PositiveRoot

/-- The terminal reflection reverses all bounded prefixes of its odd alternating word. -/
theorem alternating_reverse_prefix {n : ℕ} (alpha beta : PositiveRoot n)
    (half position : ℕ) (hposition : position ≤ 2 * half + 1) :
    alpha.alternatingProduct beta (2 * half + 1) * alpha.alternatingProduct beta position =
      alpha.alternatingProduct beta (2 * half + 1 - position) := by
  have hsum : (2 * half + 1 - position) + position = 2 * half + 1 := by omega
  have hprod := alternating_append alpha beta (2 * half + 1 - position) position
  rw [hsum] at hprod
  have hparity : Even (2 * half + 1 - position) ↔ ¬Even position := by
    rw [Nat.even_iff, Nat.even_iff]
    omega
  have htail : (if Even (2 * half + 1 - position) then
      alpha.alternatingProduct beta position else beta.alternatingProduct alpha position) =
        (alpha.alternatingProduct beta position)⁻¹ := by
    rw [alternating_inv]
    simp only [hparity]
    split_ifs <;> rfl
  rw [htail] at hprod
  rw [hprod]
  group

end Schubert.Dihedral.PositiveRoot

namespace Schubert.Dihedral

/-- The two terminal bases describe the same alternating vertex block. -/
theorem alternatingBlock_reverse {n : ℕ} (vertex : DihedralGroup n)
    (alpha beta : PositiveRoot n) (half : ℕ) :
    alternatingBlock (vertex * alpha.alternatingProduct beta (2 * half + 1)) alpha beta half =
      alternatingBlock vertex alpha beta half := by
  classical
  ext target
  rw [mem_alternatingBlock, mem_alternatingBlock]
  constructor
  · rintro ⟨position, hposition, heq⟩
    refine ⟨2 * half + 1 - position, by omega, ?_⟩
    rw [mul_assoc, PositiveRoot.alternating_reverse_prefix alpha beta half position (by omega)]
      at heq
    exact heq
  · rintro ⟨position, hposition, heq⟩
    refine ⟨2 * half + 1 - position, by omega, ?_⟩
    rw [mul_assoc, PositiveRoot.alternating_reverse_prefix alpha beta half
      (2 * half + 1 - position) (by omega)]
    have hdouble : 2 * half + 1 - (2 * half + 1 - position) = position := by omega
    rw [hdouble]
    exact heq

end Schubert.Dihedral
