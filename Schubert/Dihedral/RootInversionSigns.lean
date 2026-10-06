import Schubert.Dihedral.RootReflectionAngles
import Schubert.Dihedral.AlternatingWords
import Schubert.Dihedral.InversionArithmetic

/-! # The geometric sign criterion for canonical right inversions -/

namespace Schubert.Dihedral

/-- Negating the modular exponent interchanges the reflection distance branches. -/
theorem length_sr_neg (n : ℕ) (hthree : 3 ≤ n) (exponent : ZMod n) :
    length n hthree (.sr (-exponent)) =
      if exponent = 0 then 1 else
        min (2 * exponent.val + 1) (2 * (n - exponent.val) - 1) := by
  let : NeZero n := ⟨by omega⟩
  by_cases hzero : exponent = 0
  · rw [ite_eq_left hzero, hzero, neg_zero, length_sr, ite_eq_left rfl]
  · let : NeZero exponent := ⟨hzero⟩
    rw [ite_eq_right hzero, length_sr, ite_eq_right (neg_ne_zero.mpr hzero),
      ZMod.val_neg_of_ne_zero, min_comm]
    have hbound := exponent.val_lt
    congr 2
    omega

/-- Negating a rotation exponent preserves its shorter modular distance. -/
theorem length_r_neg (n : ℕ) (hthree : 3 ≤ n) (exponent : ZMod n) :
    length n hthree (.r (-exponent)) = 2 * min exponent.val (n - exponent.val) := by
  rw [← DihedralGroup.inv_r, length_inv, length_r]

/-- A rotation has a canonical right inversion exactly in the negative angular half-turn. -/
theorem mem_rightInversions_r_iff (n : ℕ) (hthree : 3 ≤ n)
    (exponent : ZMod n) (index : PositiveRootIndex n) :
    index ∈ rightInversions n hthree (.r exponent) ↔
      n ≤ (angularIndex index + 2 * exponent.val) % (2 * n) := by
  let : NeZero n := ⟨by omega⟩
  rw [mem_rightInversions, r_mul_rootReflection, length_sr_neg, length_r]
  have hcast : (angularIndex index : ZMod n) + exponent =
      ((angularIndex index + exponent.val : ℕ) : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [hcast]
  have hzero : ((angularIndex index + exponent.val : ℕ) : ZMod n) = 0 ↔
      (angularIndex index + exponent.val) % n = 0 := by
    rw [← ZMod.val_eq_zero, ZMod.val_natCast]
  simp only [hzero, ZMod.val_natCast]
  exact rotation_reflection_distance_lt_iff n _ _ (angularIndex_lt index) exponent.val_lt

/-- A reflection has a canonical right inversion exactly in its negative angular half-turn. -/
theorem mem_rightInversions_sr_iff (n : ℕ) (hthree : 3 ≤ n)
    (exponent : ZMod n) (index : PositiveRootIndex n) :
    index ∈ rightInversions n hthree (.sr exponent) ↔
      (angularIndex index + 2 * exponent.val) % (2 * n) = 0 ∨
        n < (angularIndex index + 2 * exponent.val) % (2 * n) := by
  let : NeZero n := ⟨by omega⟩
  rw [mem_rightInversions, sr_mul_rootReflection, length_r_neg, length_sr]
  have hcast : (angularIndex index : ZMod n) + exponent =
      ((angularIndex index + exponent.val : ℕ) : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [hcast, ZMod.val_natCast]
  simpa only [ZMod.val_eq_zero] using
    reflection_rotation_distance_lt_iff n _ _ (angularIndex_lt index) exponent.val_lt

/-- The reflected angular residue lies in the negative half-turn exactly at these residues. -/
theorem reflected_residue_ge_iff (n : ℕ) (hn : 0 < n) (position : ℤ) :
    (n : ℤ) ≤ ((n : ℤ) - position) % (2 * n : ℤ) ↔
      position % (2 * n : ℤ) = 0 ∨ (n : ℤ) < position % (2 * n : ℤ) := by
  have hnonneg := Int.emod_nonneg position (by omega : (2 * n : ℤ) ≠ 0)
  have hupper := Int.emod_lt_of_pos position (by omega : (0 : ℤ) < 2 * n)
  rw [Int.sub_emod, Int.emod_eq_of_lt (by omega : (0 : ℤ) ≤ n) (by omega)]
  by_cases hhalf : position % (2 * n : ℤ) ≤ n
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · have hneg : (n : ℤ) - position % (2 * n : ℤ) =
        -(position % (2 * n : ℤ) - n) := by ring
    rw [hneg, Int.neg_emod_eq_sub_emod, Int.emod_eq_of_lt (by omega) (by omega)]
    omega

/-- In the complete root set, negativity is equivalent to failure of positivity. -/
theorem neg_mem_positiveRoots_iff_of_mem_roots (n : ℕ) (vector : RealPlane)
    (hroot : vector ∈ roots n) :
    -vector ∈ positiveRoots n ↔ vector ∉ positiveRoots n := by
  constructor
  · intro hnegative hpositive
    obtain ⟨first, rfl⟩ := hpositive
    obtain ⟨second, hsecond⟩ := hnegative
    exact positiveRoot_ne_neg n second first hsecond
  · intro hnot
    rcases hroot with hpositive | hnegative
    · exact (hnot hpositive).elim
    · exact hnegative

/-- Canonical right inversions are exactly the positive roots with negative real image. -/
theorem mem_rightInversions_iff_negative_image (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (index : PositiveRootIndex n) :
    index ∈ rightInversions n hthree element ↔
      -(fun coordinate =>
        (vectorOperator n element (complexPositiveRoot n index) coordinate).re) ∈
          positiveRoots n := by
  let : NeZero n := ⟨by omega⟩
  have hroot := vectorOperator_realRootImage_mem_roots n element (positiveRoot n index)
    (Or.inl ⟨index, rfl⟩)
  change (fun coordinate =>
    (vectorOperator n element (complexPositiveRoot n index) coordinate).re) ∈ roots n at hroot
  rw [neg_mem_positiveRoots_iff_of_mem_roots n _ hroot]
  cases element with
  | r exponent =>
    rw [mem_rightInversions_r_iff, vectorOperator_r_mem_positiveRoots_iff]
    norm_cast
    omega
  | sr exponent =>
    rw [mem_rightInversions_sr_iff, vectorOperator_sr_mem_positiveRoots_iff]
    have hangle : (n - angularIndex index - 2 * exponent.val : ℤ) =
        (n : ℤ) - (angularIndex index + 2 * exponent.val : ℕ) := by push_cast; ring
    rw [hangle, not_lt, reflected_residue_ge_iff n (by omega)]
    norm_cast

end Schubert.Dihedral
