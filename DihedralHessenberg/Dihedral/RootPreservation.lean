import Lean.Elab.Tactic.Omega
import Mathlib.SetTheory.Cardinal.Finite
import DihedralHessenberg.Dihedral.RootGeometry
import DihedralHessenberg.Dihedral.RotationAction

/-! # Preservation of the dihedral root set

The positive angular positions cover the fundamental half-turn. The complete root set
is therefore the integer angular lattice, and the coordinate operators preserve it.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every fundamental angular position occurs among the positive roots. -/
theorem angularIndex_surjective (n : ℕ) (position : Fin n) :
    ∃ index : PositiveRootIndex n, angularIndex index = position.val := by
  let angularPosition : Fin n → Fin n := fun index => ⟨angularIndex index, angularIndex_lt index⟩
  have hinjective : Function.Injective angularPosition := by
    intro first second heq
    exact angularIndex_injective n (congrArg Fin.val heq)
  obtain ⟨index, heq⟩ :=
    (hinjective.bijective_of_nat_card_le (by rfl)).2 position
  exact ⟨index, congrArg Fin.val heq⟩

/-- Each angular position in the fundamental half-turn is a positive root. -/
theorem unitRootAt_nat_mem_positiveRoots (n position : ℕ) (hposition : position < n) :
    unitRootAt ((position : ℝ) * Real.pi / n) ∈ positiveRoots n := by
  obtain ⟨index, hindex⟩ := angularIndex_surjective n ⟨position, hposition⟩
  refine ⟨index, ?_⟩
  rw [positiveRoot, rootAngle_eq_angularIndex, hindex]

/-- A half-turn negates a real unit vector. -/
theorem unitRootAt_add_pi (angle : ℝ) :
    unitRootAt (angle + Real.pi) = -unitRootAt angle := by
  apply realPlane_ext <;> simp [unitRootAt]

/-- Every natural angular position in a full turn belongs to the complete root set. -/
theorem unitRootAt_nat_mem_roots (n position : ℕ) [NeZero n]
    (hposition : position < 2 * n) :
    unitRootAt ((position : ℝ) * Real.pi / n) ∈ roots n := by
  by_cases hhalf : position < n
  · exact Or.inl (unitRootAt_nat_mem_positiveRoots n position hhalf)
  · have hupper : position - n < n := by omega
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hangle : (position : ℝ) * Real.pi / n =
        (position - n : ℕ) * Real.pi / n + Real.pi := by
      rw [Nat.cast_sub (Nat.le_of_not_gt hhalf)]
      field_simp [hnreal]
      ring
    apply Or.inr
    change -unitRootAt ((position : ℝ) * Real.pi / n) ∈ positiveRoots n
    rw [hangle, unitRootAt_add_pi, neg_neg]
    exact unitRootAt_nat_mem_positiveRoots n (position - n) hupper

/-- Every integer angular position belongs to the complete root set. -/
theorem unitRootAt_int_mem_roots (n : ℕ) [NeZero n] (position : ℤ) :
    unitRootAt ((position : ℝ) * Real.pi / n) ∈ roots n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmodulus : (0 : ℤ) < 2 * n := by omega
  have hnonneg := Int.emod_nonneg position hmodulus.ne'
  have hupper := Int.emod_lt_of_pos position hmodulus
  let remainder : ℕ := (position % (2 * n : ℤ)).toNat
  have hremainder : (remainder : ℤ) = position % (2 * n : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hsmall : remainder < 2 * n := by omega
  have hdivision : (position : ℝ) = (remainder : ℝ) +
      2 * n * ((position / (2 * n : ℤ) : ℤ) : ℝ) := by
    have hint := Int.emod_add_mul_ediv position (2 * n : ℤ)
    rw [← hremainder] at hint
    exact_mod_cast hint.symm
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hangle : (position : ℝ) * Real.pi / n =
      (remainder : ℝ) * Real.pi / n +
        ((position / (2 * n : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hdivision]
    field_simp [hnreal]
  have hperiod : unitRootAt ((position : ℝ) * Real.pi / n) =
      unitRootAt ((remainder : ℝ) * Real.pi / n) := by
    rw [hangle]
    apply realPlane_ext <;> simp [unitRootAt]
  rw [hperiod]
  exact unitRootAt_nat_mem_roots n remainder hsmall

/-- Every member of the complete root set has an integer angular position. -/
theorem exists_int_angle_of_mem_roots (n : ℕ) [NeZero n] (vector : RealPlane)
    (hvector : vector ∈ roots n) :
    ∃ position : ℤ, vector = unitRootAt ((position : ℝ) * Real.pi / n) := by
  rcases hvector with hpositive | hnegative
  · obtain ⟨index, rfl⟩ := hpositive
    refine ⟨(angularIndex index : ℕ), ?_⟩
    rw [positiveRoot, rootAngle_eq_angularIndex]
    norm_cast
  · obtain ⟨index, hindex⟩ := hnegative
    have hvector : vector = -positiveRoot n index := by
      rw [hindex, neg_neg]
    refine ⟨((angularIndex index + n : ℕ) : ℤ), ?_⟩
    rw [hvector, positiveRoot, rootAngle_eq_angularIndex]
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hangle : (((angularIndex index + n : ℕ) : ℤ) : ℝ) * Real.pi / n =
        (angularIndex index : ℝ) * Real.pi / n + Real.pi := by
      push_cast
      field_simp [hnreal]
    rw [hangle, unitRootAt_add_pi]

/-- A coordinate rotation adds its angle to the angle of a complexified real unit vector. -/
theorem complexRotation_complexify_unitRootAt (rotationAngle rootAngle : ℝ) :
    complexRotation rotationAngle (complexify (unitRootAt rootAngle)) =
      complexify (unitRootAt (rotationAngle + rootAngle)) := by
  apply complexPlane_ext <;>
    simp [complexRotation, complexify, unitRootAt, Real.cos_add, Real.sin_add,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]

/-- Coordinate reflection sends the unit-vector angle to its supplement. -/
theorem _root_.Schubert.Dihedral.Reflection.zero_unit_root (angle : ℝ) :
    complexReflection (complexify (unitRootAt 0)) (complexify (unitRootAt angle)) =
      complexify (unitRootAt (Real.pi - angle)) := by
  apply complexPlane_ext <;>
    simp [complexReflection_apply, complexify, unitRootAt, complexBilinearForm]
  ring

/-- A modular reflection has the corresponding affine action on unit-vector angles. -/
theorem vectorOperator_sr_complexify_unitRootAt (n : ℕ) (exponent : ZMod n) (angle : ℝ) :
    vectorOperator n (.sr exponent) (complexify (unitRootAt angle)) =
      complexify (unitRootAt (Real.pi - (2 * Real.pi * exponent.val / n + angle))) := by
  rw [vectorOperator_sr, LinearMap.comp_apply, complexRotation_complexify_unitRootAt,
    _root_.Schubert.Dihedral.Reflection.zero_unit_root]

/-- The coordinate action carries each real root to the complexification of a real root. -/
theorem vectorOperator_complexify_mem_roots (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (vector : RealPlane) (hvector : vector ∈ roots n) :
    ∃ image : RealPlane, image ∈ roots n ∧
      vectorOperator n element (complexify vector) = complexify image := by
  obtain ⟨position, rfl⟩ := exists_int_angle_of_mem_roots n vector hvector
  cases element with
  | r exponent =>
    refine ⟨unitRootAt (((position + 2 * exponent.val : ℤ) : ℝ) * Real.pi / n),
      unitRootAt_int_mem_roots n _, ?_⟩
    rw [vectorOperator, complexRotation_complexify_unitRootAt]
    congr 2
    push_cast
    ring
  | sr exponent =>
    refine ⟨unitRootAt (((n - position - 2 * exponent.val : ℤ) : ℝ) * Real.pi / n),
      unitRootAt_int_mem_roots n _, ?_⟩
    rw [vectorOperator_sr_complexify_unitRootAt]
    congr 2
    push_cast
    have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp [hnreal]
    ring

/-- The real coordinates of the image of a real root form a member of the same root set. -/
theorem vectorOperator_realRootImage_mem_roots (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (vector : RealPlane) (hvector : vector ∈ roots n) :
    (fun coordinate => (vectorOperator n element (complexify vector) coordinate).re) ∈ roots n := by
  obtain ⟨image, himage, heq⟩ := vectorOperator_complexify_mem_roots n element vector hvector
  simpa only [heq, complexify, Complex.ofReal_re] using himage

/-- The coordinate action preserves the complexification of the complete real root set. -/
theorem vectorOperator_mem_complexified_roots (n : ℕ) [NeZero n]
    (element : DihedralGroup n) (vector : ComplexPlane)
    (hvector : vector ∈ complexify '' roots n) :
    vectorOperator n element vector ∈ complexify '' roots n := by
  obtain ⟨realVector, hrealVector, rfl⟩ := hvector
  obtain ⟨image, himage, heq⟩ :=
    vectorOperator_complexify_mem_roots n element realVector hrealVector
  exact ⟨image, himage, heq.symm⟩

end Schubert.Dihedral
