import DihedralHessenberg.Dihedral.RootSigns

/-! # Signs under the two simple reflections -/

namespace Schubert.Dihedral

/-- The first simple reflection preserves positivity away from its own root. -/
theorem _root_.Schubert.Dihedral.SimpleRoots.s1_image_positive_iff (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    (fun coordinate =>
      (vectorOperator n (firstSimpleReflection n) (complexPositiveRoot n index) coordinate).re) ∈
        positiveRoots n ↔ angularIndex index ≠ 0 := by
  let : NeZero n := ⟨by omega⟩
  rw [firstSimpleReflection, vectorOperator_sr_mem_positiveRoots_iff]
  simp only [ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero]
  have hindex := angularIndex_lt index
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- The second simple reflection preserves positivity away from its own root. -/
theorem _root_.Schubert.Dihedral.SimpleRoots.s2_image_positive_iff (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    (fun coordinate =>
      (vectorOperator n (secondSimpleReflection n) (complexPositiveRoot n index) coordinate).re) ∈
        positiveRoots n ↔ angularIndex index ≠ n - 1 := by
  let : NeZero n := ⟨by omega⟩
  rw [secondSimpleReflection, vectorOperator_sr_mem_positiveRoots_iff,
    ZMod.val_one'' (by omega)]
  have hindex := angularIndex_lt index
  by_cases hlast : angularIndex index = n - 1
  · rw [hlast]
    have hangle : (n - (n - 1 : ℕ) - 2 * (1 : ℕ) : ℤ) = -1 := by omega
    rw [hangle]
    have hresidue : (-1 : ℤ) % (2 * n : ℤ) = 2 * n - 1 := by
      rw [Int.neg_emod_eq_sub_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hresidue]
    omega
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega

end Schubert.Dihedral
