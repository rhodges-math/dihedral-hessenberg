import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Schubert.Dihedral.Realization

/-!
# Bilinear and reflection formulas in the coordinate plane

The complex bilinear form agrees with the real form on real vectors. Unit roots are
nonisotropic, and reflections negate their normals and fix their orthogonal hyperplanes.
-/

noncomputable section

namespace Schubert.Dihedral

theorem complexPlane_ext {first second : ComplexPlane}
    (hzero : first 0 = second 0) (hone : first 1 = second 1) : first = second := by
  ext coordinate
  fin_cases coordinate
  · exact hzero
  · exact hone

theorem realPlane_ext {first second : RealPlane}
    (hzero : first 0 = second 0) (hone : first 1 = second 1) : first = second := by
  ext coordinate
  fin_cases coordinate
  · exact hzero
  · exact hone

theorem complexBilinearForm_comm (first second : ComplexPlane) :
    complexBilinearForm first second = complexBilinearForm second first := by
  unfold complexBilinearForm
  ring

theorem complexBilinearForm_add_left (first second third : ComplexPlane) :
    complexBilinearForm (first + second) third =
      complexBilinearForm first third + complexBilinearForm second third := by
  simp only [complexBilinearForm, Pi.add_apply]
  ring

theorem complexBilinearForm_smul_left (scalar : ℂ) (first second : ComplexPlane) :
    complexBilinearForm (scalar • first) second = scalar * complexBilinearForm first second := by
  simp only [complexBilinearForm, Pi.smul_apply, smul_eq_mul]
  ring

theorem complexBilinearForm_complexify (first second : RealPlane) :
    complexBilinearForm (complexify first) (complexify second) =
      (realBilinearForm first second : ℂ) := by
  simp only [complexBilinearForm, complexify, realBilinearForm, Complex.ofReal_add,
    Complex.ofReal_mul]

/-- Complexification preserves the squared length of every real unit root. -/
theorem complexBilinearForm_unitRootAt (angle : ℝ) :
    complexBilinearForm (complexify (unitRootAt angle))
      (complexify (unitRootAt angle)) = 1 := by
  rw [complexBilinearForm_complexify, realBilinearForm_unitRootAt, Complex.ofReal_one]

/-- Every complexified positive root has squared length one. -/
theorem complexPositiveRoot_unit (n : ℕ) (index : PositiveRootIndex n) :
    complexBilinearForm (complexPositiveRoot n index) (complexPositiveRoot n index) = 1 :=
  complexBilinearForm_unitRootAt (rootAngle n index)

/-- Positive roots are nonisotropic for the complex bilinear form. -/
theorem complexPositiveRoot_nonisotropic (n : ℕ) (index : PositiveRootIndex n) :
    complexBilinearForm (complexPositiveRoot n index) (complexPositiveRoot n index) ≠ 0 := by
  rw [complexPositiveRoot_unit]
  exact one_ne_zero

theorem complexPairing_apply (normal vector : ComplexPlane) :
    complexPairing normal vector = complexBilinearForm vector normal := by
  simp [complexPairing, complexBilinearForm, mul_comm]

/-- A reflection subtracts twice the orthogonal component in the normal direction. -/
theorem complexReflection_apply (normal vector : ComplexPlane) :
    complexReflection normal vector =
      vector - (2 * complexBilinearForm vector normal /
        complexBilinearForm normal normal) • normal := by
  ext coordinate
  simp [complexReflection, complexPairing_apply, div_eq_mul_inv]
  ring

/-- A nonisotropic reflection negates its normal vector. -/
theorem complexReflection_normal (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    complexReflection normal normal = -normal := by
  rw [complexReflection_apply]
  ext coordinate
  simp [hnormal]
  ring

/-- A reflection fixes every vector orthogonal to its normal. -/
theorem complexReflection_orthogonal (normal vector : ComplexPlane)
    (horthogonal : complexBilinearForm vector normal = 0) :
    complexReflection normal vector = vector := by
  rw [complexReflection_apply, horthogonal]
  simp

/-- Reflection negates the bilinear pairing with its normal. -/
theorem complexReflection_pairing (normal vector : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    complexBilinearForm (complexReflection normal vector) normal =
      -complexBilinearForm vector normal := by
  rw [← complexPairing_apply, complexReflection_apply, map_sub, map_smul]
  simp only [complexPairing_apply, smul_eq_mul]
  field_simp [hnormal]
  ring

/-- A reflection with nonisotropic normal is an involution. -/
theorem complexReflection_involutive (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    Function.Involutive (complexReflection normal) := by
  intro vector
  rw [complexReflection_apply, complexReflection_pairing normal vector hnormal,
    complexReflection_apply]
  ext coordinate
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A nonisotropic reflection as an invertible linear operator. -/
def complexReflectionEquiv (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) : ComplexPlane ≃ₗ[ℂ] ComplexPlane :=
  LinearEquiv.ofInvolutive (complexReflection normal)
    (complexReflection_involutive normal hnormal)

theorem complexRotation_zero : complexRotation 0 = LinearMap.id := by
  ext vector coordinate
  fin_cases coordinate <;> simp [complexRotation]

/-- Successive rotations compose by adding their angles. -/
theorem complexRotation_add (first second : ℝ) :
    complexRotation (first + second) =
      (complexRotation first).comp (complexRotation second) := by
  ext vector coordinate
  fin_cases coordinate <;>
    simp [complexRotation, Real.cos_add, Real.sin_add, Complex.ofReal_add,
      Complex.ofReal_sub, Complex.ofReal_mul] <;> ring

end Schubert.Dihedral
