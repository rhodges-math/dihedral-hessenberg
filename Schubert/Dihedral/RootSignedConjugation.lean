import Schubert.Dihedral.RootAngularEquality

/-! # Sign-independent conjugation of indexed root reflections -/

namespace Schubert.Dihedral

/-- Equality with a negative root still determines its angular position modulo n. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.negative_angle_cast (n : ℕ) [NeZero n]
    (position : ℤ) (index : PositiveRootIndex n)
    (heq : unitRootAt ((position : ℝ) * Real.pi / n) = -positiveRoot n index) :
    (position : ZMod n) = (angularIndex index : ZMod n) := by
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hangle : (((position + n : ℤ) : ℝ) * Real.pi / n) =
      (position : ℝ) * Real.pi / n + Real.pi := by
    push_cast
    field_simp [hnreal]
  have hpositive : unitRootAt (((position + n : ℤ) : ℝ) * Real.pi / n) =
      positiveRoot n index := by
    rw [hangle, unitRootAt_add_pi, heq, neg_neg]
  have hcast := _root_.Schubert.Dihedral.IndexedRoots.positive_angle_cast n (position + n) index
    hpositive
  simpa only [Int.cast_add, Int.cast_natCast, ZMod.natCast_self, add_zero] using hcast

/-- A negative root image has the same conjugated reflection as its positive opposite. -/
theorem rootReflection_of_negative_image (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (index image : PositiveRootIndex n)
    (himage : vectorOperator n element (complexPositiveRoot n index) =
      -complexPositiveRoot n image) :
    rootReflection image = element * rootReflection index * element⁻¹ := by
  have hnegative : -complexPositiveRoot n image = complexify (-positiveRoot n image) := by
    funext coordinate
    simp [complexPositiveRoot, complexify]
  rw [hnegative] at himage
  cases element with
  | r exponent =>
    rw [vectorOperator_r_complexPositiveRoot] at himage
    have hroot := complexify_injective himage
    have hint : unitRootAt
        ((((angularIndex index + 2 * exponent.val : ℕ) : ℤ) : ℝ) * Real.pi / n) =
          -positiveRoot n image := by
      simpa only [Int.cast_natCast] using hroot
    have hcast := _root_.Schubert.Dihedral.IndexedRoots.negative_angle_cast n _ image hint
    push_cast at hcast
    simp only [ZMod.natCast_zmod_val] at hcast
    rw [rootReflection_eq_sr_neg_angularIndex, rootReflection_eq_sr_neg_angularIndex,
      DihedralGroup.inv_r, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    rw [← hcast]
    ring
  | sr exponent =>
    rw [vectorOperator_sr_complexPositiveRoot] at himage
    have hroot := complexify_injective himage
    have hcast := _root_.Schubert.Dihedral.IndexedRoots.negative_angle_cast n _ image hroot
    push_cast at hcast
    simp only [ZMod.natCast_self, ZMod.natCast_zmod_val] at hcast
    rw [rootReflection_eq_sr_neg_angularIndex, rootReflection_eq_sr_neg_angularIndex,
      DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
    congr 1
    rw [← hcast]
    ring

/-- Either sign of a root image identifies the conjugated indexed reflection. -/
theorem rootReflection_of_signed_image (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (index image : PositiveRootIndex n)
    (himage : vectorOperator n element (complexPositiveRoot n index) =
      complexPositiveRoot n image ∨
        vectorOperator n element (complexPositiveRoot n index) = -complexPositiveRoot n image) :
    rootReflection image = element * rootReflection index * element⁻¹ := by
  rcases himage with hpositive | hnegative
  · exact rootReflection_of_positive_image n element index image hpositive
  · exact rootReflection_of_negative_image n element index image hnegative

/-- Either sign of a root image identifies the corresponding right and left reflection endpoints. -/
theorem rootReflection_endpoint_of_signed_image (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (index image : PositiveRootIndex n)
    (himage : vectorOperator n element (complexPositiveRoot n index) =
      complexPositiveRoot n image ∨
        vectorOperator n element (complexPositiveRoot n index) = -complexPositiveRoot n image) :
    element * rootReflection index = rootReflection image * element := by
  rw [rootReflection_of_signed_image n element index image himage]
  group

end Schubert.Dihedral
