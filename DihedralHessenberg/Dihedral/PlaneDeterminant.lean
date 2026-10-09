import Mathlib.LinearAlgebra.Determinant
import DihedralHessenberg.Dihedral.PlaneCharacter

/-! # Determinants of the planar dihedral realization

Rotations have determinant one and nonisotropic normal reflections determinant minus one.
These are the values of the determinant character of the plane representation.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Coordinate rotation preserves the determinant of the plane. -/
theorem complexRotation_det (angle : ℝ) : LinearMap.det (complexRotation angle) = 1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 2))]
  rw [Matrix.det_fin_two]
  simp [complexRotation]
  have htrig := Complex.cos_sq_add_sin_sq (angle : ℂ)
  linear_combination htrig

/-- Every nonisotropic normal reflection reverses the plane determinant. -/
theorem complexReflection_det (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    LinearMap.det (complexReflection normal) = -1 := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 2))]
  simp [complexReflection, complexPairing_apply, complexBilinearForm, Matrix.det_fin_two]
  dsimp [complexBilinearForm] at hnormal
  have hnorm : normal 0 ^ 2 + normal 1 ^ 2 ≠ 0 := by
    simpa [pow_two] using hnormal
  field_simp [hnormal, hnorm]
  ring

/-- Rotations have determinant one in the vector representation. -/
theorem vectorRepresentation_det_r (n : ℕ) [NeZero n] (exponent : ZMod n) :
    LinearMap.det (vectorRepresentation n (.r exponent)) = 1 := complexRotation_det _

/-- Reflections have determinant minus one in the vector representation. -/
theorem vectorRepresentation_det_sr (n : ℕ) [NeZero n] (exponent : ZMod n) :
    LinearMap.det (vectorRepresentation n (.sr exponent)) = -1 := by
  apply complexReflection_det
  rw [complexBilinearForm_unitRootAt]
  exact one_ne_zero

end Schubert.Dihedral
