import DihedralHessenberg.Dihedral.FirstBlockStabilizer
import DihedralHessenberg.Dihedral.SecondBlockStabilizer
import DihedralHessenberg.Dihedral.RootCosetObjects
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Standard action stabilizers of alternating vertex blocks -/

namespace Schubert.Dihedral

open scoped Pointwise

/-- The reflection-generated subgroup contains exactly identity and the reflection. -/
theorem PositiveRoot.mem_subgroup {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (element : DihedralGroup n) :
    element ∈ alpha.subgroup ↔ element = 1 ∨ element = alpha.reflection := by
  change element ∈ Subgroup.closure {rootReflection alpha.index} ↔
    element = 1 ∨ element = rootReflection alpha.index
  rw [rootReflection_eq_sr]
  exact mem_closure_sr_iff n _ element

/-- The standard left-action stabilizer of the first block is its terminal subgroup. -/
theorem first_block_subgroup {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    MulAction.stabilizer (DihedralGroup n)
      (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half) =
        (positiveRootEquiv n ⟨2 * half, by omega⟩).subgroup := by
  ext element
  rw [MulAction.mem_stabilizer_iff, PositiveRoot.mem_subgroup]
  exact first_block_stabilizer half hbound element

/-- The standard left-action stabilizer of the second block is its terminal subgroup. -/
theorem second_block_subgroup {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    MulAction.stabilizer (DihedralGroup n)
      (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half) =
        (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).subgroup := by
  ext element
  rw [MulAction.mem_stabilizer_iff, PositiveRoot.mem_subgroup]
  exact second_block_stabilizer half hbound element

end Schubert.Dihedral
