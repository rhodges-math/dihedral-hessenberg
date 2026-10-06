import Mathlib.RepresentationTheory.Character
import Schubert.Dihedral.RotationAction

/-! # Characters of the planar dihedral realization

The trace of rotation is twice its cosine, while every normal reflection has trace zero
on the two-dimensional coordinate plane.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Coordinate rotation has trace twice the cosine of its angle. -/
theorem complexRotation_trace (angle : ℝ) :
    LinearMap.trace ℂ ComplexPlane (complexRotation angle) = 2 * (Real.cos angle : ℂ) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2))]
  simp [Matrix.trace, complexRotation, Fin.sum_univ_two]
  ring

/-- A nonisotropic normal reflection has trace zero in the coordinate plane. -/
theorem complexReflection_trace (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    LinearMap.trace ℂ ComplexPlane (complexReflection normal) = 0 := by
  rw [complexReflection, map_sub, map_smul, LinearMap.trace_smulRight, complexPairing_apply]
  simp [hnormal]

/-- The defining dihedral representation has the usual rotation character value. -/
theorem vectorRepresentation_character_r (n : ℕ) [NeZero n] (exponent : ZMod n) :
    (vectorRepresentation n).character (.r exponent) =
      2 * (Real.cos (2 * Real.pi * exponent.val / n) : ℂ) :=
  complexRotation_trace _

/-- The defining dihedral representation has zero character on every reflection. -/
theorem vectorRepresentation_character_sr (n : ℕ) [NeZero n] (exponent : ZMod n) :
    (vectorRepresentation n).character (.sr exponent) = 0 := by
  apply complexReflection_trace
  rw [complexBilinearForm_unitRootAt]
  exact one_ne_zero

end Schubert.Dihedral
