import DihedralHessenberg.Dihedral.RootSigns
import DihedralHessenberg.Dihedral.RootReflectionAngles
import DihedralHessenberg.Dihedral.RootInversionSigns

/-! # Recovering angular positions from equality with a positive root -/

namespace Schubert.Dihedral

/-- Equality with a positive root determines the full-turn integer angular residue. -/
theorem unitRootAt_int_eq_positiveRoot_iff (n : ℕ) [NeZero n] (position : ℤ)
    (index : PositiveRootIndex n) :
    unitRootAt ((position : ℝ) * Real.pi / n) = positiveRoot n index ↔
      position % (2 * n : ℤ) = angularIndex index := by
  constructor
  · intro heq
    have hpositive : unitRootAt ((position : ℝ) * Real.pi / n) ∈ positiveRoots n :=
      ⟨index, heq.symm⟩
    have hupper := (unitRootAt_int_mem_positiveRoots_iff n position).mp hpositive
    have hnonneg := Int.emod_nonneg position (by
      have hn := NeZero.ne n
      omega : (2 * n : ℤ) ≠ 0)
    let remainder := (position % (2 * n : ℤ)).toNat
    have hremainder : (remainder : ℤ) = position % (2 * n : ℤ) :=
      Int.toNat_of_nonneg hnonneg
    have hsmall : remainder < n := by omega
    obtain ⟨other, hother⟩ := angularIndex_surjective n ⟨remainder, hsmall⟩
    have hroots : positiveRoot n other = positiveRoot n index := by
      rw [positiveRoot, rootAngle_eq_angularIndex, hother]
      rw [unitRootAt_int_eq_emod, ← hremainder] at heq
      norm_cast at heq
    have hindices := positiveRoot_injective n hroots
    rw [hindices] at hother
    change angularIndex index = remainder at hother
    omega
  · intro hposition
    rw [unitRootAt_int_eq_emod, hposition, positiveRoot, rootAngle_eq_angularIndex]
    norm_cast

/-- Equality with a positive root determines the angular position modulo n. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.positive_angle_cast (n : ℕ) [NeZero n]
    (position : ℤ) (index : PositiveRootIndex n)
    (heq : unitRootAt ((position : ℝ) * Real.pi / n) = positiveRoot n index) :
    (position : ZMod n) = (angularIndex index : ZMod n) := by
  have hresidue := (unitRootAt_int_eq_positiveRoot_iff n position index).mp heq
  have hdivision := Int.emod_add_mul_ediv position (2 * n : ℤ)
  have hcast := congrArg (fun value : ℤ => (value : ZMod n)) hdivision
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    ZMod.natCast_self, mul_zero, zero_mul, add_zero] at hcast
  rw [hresidue, Int.cast_natCast] at hcast
  exact hcast.symm

/-- A positive root image has the conjugated indexed reflection. -/
theorem rootReflection_of_positive_image (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (index image : PositiveRootIndex n)
    (himage : vectorOperator n element (complexPositiveRoot n index) =
      complexPositiveRoot n image) :
    rootReflection image = element * rootReflection index * element⁻¹ := by
  cases element with
  | r exponent =>
    rw [vectorOperator_r_complexPositiveRoot] at himage
    have hroot := complexify_injective himage
    have hint : unitRootAt
        ((((angularIndex index + 2 * exponent.val : ℕ) : ℤ) : ℝ) * Real.pi / n) =
          positiveRoot n image := by
      simpa only [Int.cast_natCast] using hroot
    have hcast := _root_.Schubert.Dihedral.IndexedRoots.positive_angle_cast n _ image hint
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
    have hcast := _root_.Schubert.Dihedral.IndexedRoots.positive_angle_cast n _ image hroot
    push_cast at hcast
    simp only [ZMod.natCast_self, ZMod.natCast_zmod_val] at hcast
    rw [rootReflection_eq_sr_neg_angularIndex, rootReflection_eq_sr_neg_angularIndex,
      DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
    congr 1
    rw [← hcast]
    ring

/-- Every non-inverted positive root has a positive image with the conjugated reflection. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.positive_image_of_not_mem (n : ℕ) (hthree : 3 ≤
  n)
    (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hnot : index ∉ rightInversions n hthree element) :
    ∃ image : PositiveRootIndex n,
      vectorOperator n element (complexPositiveRoot n index) = complexPositiveRoot n image ∧
        rootReflection image = element * rootReflection index * element⁻¹ := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨image, hroot, himage⟩ := vectorOperator_complexify_mem_roots n element
    (positiveRoot n index) (Or.inl ⟨index, rfl⟩)
  change vectorOperator n element (complexPositiveRoot n index) = complexify image at himage
  have hpositive : image ∈ positiveRoots n := by
    rcases hroot with hpositive | hnegative
    · exact hpositive
    · apply False.elim
      apply hnot
      apply (mem_rightInversions_iff_negative_image n hthree element index).mpr
      change -image ∈ positiveRoots n at hnegative
      simpa only [himage, complexify, Complex.ofReal_re] using hnegative
  obtain ⟨other, hother⟩ := hpositive
  rw [← hother] at himage
  exact ⟨other, himage, rootReflection_of_positive_image n element index other himage⟩

end Schubert.Dihedral
