import Lean.Elab.Tactic.Omega
import Schubert.Dihedral.ReflectionIndex
import Schubert.Dihedral.RotationAction

/-!
# Indexed root reflections and coordinate operators

This file bridges the alternating positive-root numbering with the modular reflection
coordinate. It preserves the angle convention exactly.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Negating a normal does not change its reflection. -/
theorem complexReflection_neg (normal : ComplexPlane) :
    complexReflection (-normal) = complexReflection normal := by
  apply LinearMap.ext
  intro vector
  funext coordinate
  simp only [complexReflection_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.neg_apply, complexBilinearForm]
  ring_nf

/-- Increasing a unit-root angle by a half-turn negates its normal. -/
theorem complexify_unitRootAt_add_pi (angle : ℝ) :
    complexify (unitRootAt (angle + Real.pi)) = -complexify (unitRootAt angle) := by
  apply complexPlane_ext <;> simp [complexify, unitRootAt]

/-- Unit-root reflections are invariant under a half-turn in the normal angle. -/
theorem complexReflection_unitRootAt_add_pi (angle : ℝ) :
    complexReflection (complexify (unitRootAt (angle + Real.pi))) =
      complexReflection (complexify (unitRootAt angle)) := by
  rw [complexify_unitRootAt_add_pi, complexReflection_neg]

/-- A natural modular reflection coordinate uses its unreduced rotation angle. -/
theorem vectorOperator_sr_natCast (n exponent : ℕ) [NeZero n] :
    vectorOperator n (.sr (exponent : ZMod n)) =
      (complexReflection (complexify (unitRootAt 0))).comp
        (complexRotation (2 * Real.pi * exponent / n)) := by
  rw [vectorOperator_sr, ZMod.val_natCast, complexRotation_nat_mod n _ (NeZero.ne n)]

/-- A negative natural reflection coordinate has the positive fundamental root angle. -/
theorem vectorOperator_sr_neg_natCast (n exponent : ℕ) [NeZero n] :
    vectorOperator n (.sr (-(exponent : ZMod n))) =
      complexReflection (complexify (unitRootAt ((exponent : ℝ) * Real.pi / n))) := by
  rw [vectorOperator_sr, complexRotation_zmod_neg, ZMod.val_natCast,
    complexReflection_zero_comp_rotation, neg_neg,
    complexRotation_nat_mod n _ (NeZero.ne n)]
  conv_rhs => rw [complexReflection_unitRootAt]
  have hangle : -2 * ((exponent : ℝ) * Real.pi / n) =
      -(2 * Real.pi * exponent / n) := by ring
  rw [hangle]
  simpa only [neg_neg] using
    (complexReflection_zero_comp_rotation (-(2 * Real.pi * exponent / n))).symm

/-- A positive natural reflection coordinate has the negative fundamental root angle. -/
theorem vectorOperator_sr_natCast_reflection (n exponent : ℕ) [NeZero n] :
    vectorOperator n (.sr (exponent : ZMod n)) =
      complexReflection (complexify (unitRootAt (-((exponent : ℝ) * Real.pi / n)))) := by
  rw [vectorOperator_sr_natCast]
  conv_rhs => rw [complexReflection_unitRootAt]
  congr 1
  congr 1
  ring

/-- The indexed group reflection acts by reflection in its positive unit root. -/
theorem vectorOperator_rootReflection (n : ℕ) (index : PositiveRootIndex n) :
    vectorOperator n (rootReflection index) =
      complexReflection (complexPositiveRoot n index) := by
  have hn : n ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) index.isLt).ne'
  let : NeZero n := ⟨hn⟩
  unfold complexPositiveRoot positiveRoot rootAngle
  by_cases heven : index.val % 2 = 0
  · rw [ite_eq_left heven, rootReflection_eq_sr_of_even index heven,
      vectorOperator_sr_neg_natCast]
  · rw [ite_eq_right heven, rootReflection_eq_sr_of_odd index heven]
    have hcoordinate : ((index.val / 2 : ℕ) : ZMod n) + 1 =
        ((index.val / 2 + 1 : ℕ) : ZMod n) := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [hcoordinate, vectorOperator_sr_natCast_reflection]
    have hbound : 1 + index.val / 2 ≤ n := by
      have := index.isLt
      omega
    have hnat : n - 1 - index.val / 2 = n - (1 + index.val / 2) := by omega
    have hangle : (n - 1 - index.val / 2 : ℕ) * Real.pi / n =
        -(((index.val / 2 + 1 : ℕ) : ℝ) * Real.pi / n) + Real.pi := by
      rw [hnat, Nat.cast_sub hbound]
      push_cast
      have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp [hnreal]
      ring
    rw [hangle, complexReflection_unitRootAt_add_pi]

/-- Polynomial action of an indexed reflection is the normal substitution. -/
theorem polynomialAction_rootReflection (n : ℕ) [NeZero n]
    (index : PositiveRootIndex n) :
    (polynomialAction n (rootReflection index)).toAlgHom =
      polynomialSubstitution (complexReflection (complexPositiveRoot n index)) := by
  change polynomialSubstitution (vectorOperator n (rootReflection index)) = _
  rw [vectorOperator_rootReflection]

end Schubert.Dihedral
