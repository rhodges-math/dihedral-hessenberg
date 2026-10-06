import Mathlib.Tactic.LinearCombination
import Schubert.Dihedral.RotationAction

/-! # Auxiliary complex polynomial coordinates

The coordinates u = x + i*y and v = x - i*y diagonalize the column-substitution action
of rotations. They form an invertible change of coordinates within the existing algebra.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The auxiliary coordinate x + i*y in the coordinate polynomial algebra. -/
def auxiliaryU : CoordinatePolynomial :=
  MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1

/-- The auxiliary coordinate x - i*y in the coordinate polynomial algebra. -/
def auxiliaryV : CoordinatePolynomial :=
  MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1

/-- The first auxiliary coordinate is the polynomial of the vector (1,i). -/
theorem auxiliaryU_eq_linearPolynomial : auxiliaryU = linearPolynomial ![1, Complex.I] := by
  simp [auxiliaryU, linearPolynomial]

/-- The second auxiliary coordinate is the polynomial of the vector (1,-i). -/
theorem auxiliaryV_eq_linearPolynomial : auxiliaryV = linearPolynomial ![1, -Complex.I] := by
  simp [auxiliaryV, linearPolynomial, sub_eq_add_neg]

/-- Rotation acts on the first auxiliary coordinate with the negative-angle eigenvalue. -/
theorem _root_.Schubert.Dihedral.Axial.subst_rotation_u (angle : ℝ) :
    polynomialSubstitution (complexRotation angle) auxiliaryU =
      MvPolynomial.C ((Real.cos angle : ℂ) - Complex.I * Real.sin angle) * auxiliaryU := by
  rw [auxiliaryU_eq_linearPolynomial, polynomialSubstitution_linearPolynomial]
  rw [← linearPolynomial_smul]
  congr 1
  apply complexPlane_ext
  · simp [complexRotation, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [complexRotation, Pi.smul_apply, smul_eq_mul]
    linear_combination Complex.sin (angle : ℂ) * Complex.I_sq

/-- Rotation acts on the second auxiliary coordinate with the positive-angle eigenvalue. -/
theorem _root_.Schubert.Dihedral.Axial.subst_rotation_v (angle : ℝ) :
    polynomialSubstitution (complexRotation angle) auxiliaryV =
      MvPolynomial.C ((Real.cos angle : ℂ) + Complex.I * Real.sin angle) * auxiliaryV := by
  rw [auxiliaryV_eq_linearPolynomial, polynomialSubstitution_linearPolynomial]
  rw [← linearPolynomial_smul]
  congr 1
  apply complexPlane_ext
  · simp [complexRotation, Pi.smul_apply, smul_eq_mul]
    ring
  · simp [complexRotation, Pi.smul_apply, smul_eq_mul]
    linear_combination Complex.sin (angle : ℂ) * Complex.I_sq

/-- The first auxiliary-coordinate rotation eigenvalue is the negative-angle exponential. -/
theorem _root_.Schubert.Dihedral.Axial.subst_rotation_u_exp (angle : ℝ) :
    polynomialSubstitution (complexRotation angle) auxiliaryU =
      MvPolynomial.C (Complex.exp (((-angle : ℝ) : ℂ) * Complex.I)) * auxiliaryU := by
  rw [_root_.Schubert.Dihedral.Axial.subst_rotation_u, Complex.exp_ofReal_mul_I]
  simp [mul_comm, sub_eq_add_neg]

/-- The second auxiliary-coordinate rotation eigenvalue is the positive-angle exponential. -/
theorem _root_.Schubert.Dihedral.Axial.subst_rotation_v_exp (angle : ℝ) :
    polynomialSubstitution (complexRotation angle) auxiliaryV =
      MvPolynomial.C (Complex.exp ((angle : ℂ) * Complex.I)) * auxiliaryV := by
  rw [_root_.Schubert.Dihedral.Axial.subst_rotation_v, Complex.exp_ofReal_mul_I]
  rw [mul_comm Complex.I]

/-- A dihedral rotation acts on u with the negative-angle exponential eigenvalue. -/
theorem polynomialAction_r_auxiliaryU (n : ℕ) [NeZero n] (exponent : ZMod n) :
    polynomialAction n (.r exponent) auxiliaryU =
      MvPolynomial.C (Complex.exp
        (((-(2 * Real.pi * exponent.val / n) : ℝ) : ℂ) * Complex.I)) * auxiliaryU := by
  rw [polynomialAction_apply]
  exact _root_.Schubert.Dihedral.Axial.subst_rotation_u_exp _

/-- A dihedral rotation acts on v with the positive-angle exponential eigenvalue. -/
theorem polynomialAction_r_auxiliaryV (n : ℕ) [NeZero n] (exponent : ZMod n) :
    polynomialAction n (.r exponent) auxiliaryV =
      MvPolynomial.C (Complex.exp
        (((2 * Real.pi * exponent.val / n : ℝ) : ℂ) * Complex.I)) * auxiliaryV := by
  rw [polynomialAction_apply]
  exact _root_.Schubert.Dihedral.Axial.subst_rotation_v_exp _

/-- Coordinate reflection carries u to -v. -/
theorem _root_.Schubert.Dihedral.Axial.subst_reflection_u :
    polynomialSubstitution (complexReflection (complexify (unitRootAt 0))) auxiliaryU =
      -auxiliaryV := by
  rw [auxiliaryU_eq_linearPolynomial, polynomialSubstitution_linearPolynomial]
  simp [complexReflection_apply, complexBilinearForm, complexify, unitRootAt,
    linearPolynomial, auxiliaryV, map_ofNat]
  ring

/-- Coordinate reflection carries v to -u. -/
theorem _root_.Schubert.Dihedral.Axial.subst_reflection_v :
    polynomialSubstitution (complexReflection (complexify (unitRootAt 0))) auxiliaryV =
      -auxiliaryU := by
  rw [auxiliaryV_eq_linearPolynomial, polynomialSubstitution_linearPolynomial]
  simp [complexReflection_apply, complexBilinearForm, complexify, unitRootAt,
    linearPolynomial, auxiliaryU, map_ofNat]
  ring

/-- Substitution of the two auxiliary coordinates for the variables. -/
def auxiliaryCoordinateHom : CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial :=
  MvPolynomial.aeval ![auxiliaryU, auxiliaryV]

/-- The inverse substitution x = (u+v)/2 and y = (u-v)/(2i). -/
def auxiliaryCoordinateInverseHom : CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial :=
  MvPolynomial.aeval ![
    MvPolynomial.C ((2 : ℂ)⁻¹) * (MvPolynomial.X 0 + MvPolynomial.X 1),
    MvPolynomial.C (-Complex.I / 2) * (MvPolynomial.X 0 - MvPolynomial.X 1)]

/-- The scalar in the inverse second coordinate is 1/(2i). -/
theorem auxiliaryCoordinateInverse_scalar : (-Complex.I / 2 : ℂ) = 1 / (2 * Complex.I) := by
  field_simp
  simp [Complex.I_sq]

/-- Applying auxiliary substitution after its inverse recovers every polynomial. -/
theorem auxiliaryCoordinateHom_comp_inverse :
    auxiliaryCoordinateHom.comp auxiliaryCoordinateInverseHom =
      AlgHom.id ℂ CoordinatePolynomial := by
  have hhalf : (MvPolynomial.C ((2 : ℂ)⁻¹) : CoordinatePolynomial) * 2 = 1 := by
    change MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.C (2 : ℂ) = _
    rw [← map_mul]
    norm_num
  have hI : (MvPolynomial.C Complex.I : CoordinatePolynomial) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  ext coordinate : 1
  fin_cases coordinate <;>
    simp [auxiliaryCoordinateHom, auxiliaryCoordinateInverseHom, auxiliaryU, auxiliaryV,
      div_eq_mul_inv]
  · linear_combination MvPolynomial.X (0 : Fin 2) * hhalf
  · linear_combination -2 * MvPolynomial.C ((2 : ℂ)⁻¹) *
      MvPolynomial.X (1 : Fin 2) * hI + MvPolynomial.X (1 : Fin 2) * hhalf

/-- Applying inverse substitution after auxiliary substitution recovers every polynomial. -/
theorem auxiliaryCoordinateInverseHom_comp :
    auxiliaryCoordinateInverseHom.comp auxiliaryCoordinateHom =
      AlgHom.id ℂ CoordinatePolynomial := by
  have hhalf : (MvPolynomial.C ((2 : ℂ)⁻¹) : CoordinatePolynomial) * 2 = 1 := by
    change MvPolynomial.C ((2 : ℂ)⁻¹) * MvPolynomial.C (2 : ℂ) = _
    rw [← map_mul]
    norm_num
  have hI : (MvPolynomial.C Complex.I : CoordinatePolynomial) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  ext coordinate : 1
  fin_cases coordinate <;>
    simp [auxiliaryCoordinateHom, auxiliaryCoordinateInverseHom, auxiliaryU, auxiliaryV,
      div_eq_mul_inv]
  · linear_combination -MvPolynomial.C ((2 : ℂ)⁻¹) *
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X 1) * hI + MvPolynomial.X 0 * hhalf
  · linear_combination MvPolynomial.C ((2 : ℂ)⁻¹) *
      (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X 1) * hI + MvPolynomial.X 1 * hhalf

/-- The auxiliary coordinates give an algebra automorphism of the polynomial model. -/
def auxiliaryCoordinateEquiv : CoordinatePolynomial ≃ₐ[ℂ] CoordinatePolynomial :=
  AlgEquiv.ofAlgHom auxiliaryCoordinateHom auxiliaryCoordinateInverseHom
    auxiliaryCoordinateHom_comp_inverse auxiliaryCoordinateInverseHom_comp

/-- The coordinate change sends the first variable to u. -/
theorem auxiliaryCoordinateEquiv_X_zero : auxiliaryCoordinateEquiv (MvPolynomial.X 0) =
    auxiliaryU := by
  change auxiliaryCoordinateHom (MvPolynomial.X 0) = _
  simp [auxiliaryCoordinateHom]

/-- The coordinate change sends the second variable to v. -/
theorem auxiliaryCoordinateEquiv_X_one : auxiliaryCoordinateEquiv (MvPolynomial.X 1) =
    auxiliaryV := by
  change auxiliaryCoordinateHom (MvPolynomial.X 1) = _
  simp [auxiliaryCoordinateHom]

/-- The inverse coordinate change sends x to (x+y)/2 in the target coordinates. -/
theorem auxiliaryCoordinateEquiv_symm_X_zero :
    auxiliaryCoordinateEquiv.symm (MvPolynomial.X 0) =
      MvPolynomial.C ((2 : ℂ)⁻¹) * (MvPolynomial.X 0 + MvPolynomial.X 1) := by
  change auxiliaryCoordinateInverseHom (MvPolynomial.X 0) = _
  simp [auxiliaryCoordinateInverseHom]

/-- The inverse coordinate change sends y to (x-y)/(2i) in the target coordinates. -/
theorem auxiliaryCoordinateEquiv_symm_X_one :
    auxiliaryCoordinateEquiv.symm (MvPolynomial.X 1) =
      MvPolynomial.C (1 / (2 * Complex.I)) * (MvPolynomial.X 0 - MvPolynomial.X 1) := by
  change auxiliaryCoordinateInverseHom (MvPolynomial.X 1) = _
  simp [auxiliaryCoordinateInverseHom, auxiliaryCoordinateInverse_scalar]

end Schubert.Dihedral
