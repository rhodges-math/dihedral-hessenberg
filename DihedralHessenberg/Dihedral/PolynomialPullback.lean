import DihedralHessenberg.Dihedral.RotationAction

/-! # Column substitution as inverse geometric pullback -/

noncomputable section
namespace Schubert.Dihedral

/-- Complexified real rotations preserve the standard symmetric bilinear form. -/
theorem rotation_bilinear (angle : ℝ) (first second : ComplexPlane) :
    complexBilinearForm (complexRotation angle first) (complexRotation angle second) =
      complexBilinearForm first second := by
  have hunit : (Real.cos angle : ℂ) ^ 2 + (Real.sin angle : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq angle
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at hunit
  simp [complexRotation, complexBilinearForm]
  linear_combination (first 0 * second 0 + first 1 * second 1) * hunit

/-- Every dihedral operator preserves the symmetric bilinear form. -/
theorem operator_bilinear (n : ℕ) (element : DihedralGroup n)
    (first second : ComplexPlane) :
    complexBilinearForm (vectorOperator n element first) (vectorOperator n element second) =
      complexBilinearForm first second := by
  have hreflection : ∀ first second : ComplexPlane,
      complexBilinearForm (complexReflection (complexify (unitRootAt 0)) first)
        (complexReflection (complexify (unitRootAt 0)) second) =
          complexBilinearForm first second := by
    intro first second
    simp [complexReflection_apply, complexBilinearForm, unitRootAt, complexify]
    ring
  cases element with
  | r coordinate => exact rotation_bilinear _ first second
  | sr coordinate =>
      rw [vectorOperator_sr, LinearMap.comp_apply, LinearMap.comp_apply, hreflection]
      exact rotation_bilinear _ first second

/-- A column operator on a linear form pairs with the inverse geometric action. -/
theorem operator_pairing_inverse (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (vector point : ComplexPlane) :
    complexBilinearForm (vectorOperator n element vector) point =
      complexBilinearForm vector (vectorOperator n element⁻¹ point) := by
  have hinverse : vectorOperator n element⁻¹ (vectorOperator n element vector) = vector := by
    rw [← LinearMap.comp_apply, ← vectorOperator_mul, inv_mul_cancel,
      vectorOperator_one, LinearMap.id_apply]
  have hpair := operator_bilinear n element⁻¹ (vectorOperator n element vector) point
  rw [hinverse] at hpair
  exact hpair.symm

/-- The coordinate of the inverse geometric action on formal coordinate variables. -/
def inverseCoordinate (n : ℕ) (element : DihedralGroup n) (coordinate : Fin 2) :
    CoordinatePolynomial :=
  MvPolynomial.C (vectorOperator n element⁻¹ (coordinateBasisVector 0) coordinate) *
      MvPolynomial.X 0 +
    MvPolynomial.C (vectorOperator n element⁻¹ (coordinateBasisVector 1) coordinate) *
      MvPolynomial.X 1

/-- Column substitution is exactly inverse geometric substitution on every variable. -/
theorem polynomialAction_inverse_X (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (coordinate : Fin 2) :
    polynomialAction n element (MvPolynomial.X coordinate) =
      inverseCoordinate n element coordinate := by
  rw [← linearPolynomial_basis coordinate, polynomialAction_linearPolynomial]
  have hzero := operator_pairing_inverse n element (coordinateBasisVector coordinate)
    (coordinateBasisVector 0)
  have hone := operator_pairing_inverse n element (coordinateBasisVector coordinate)
    (coordinateBasisVector 1)
  fin_cases coordinate <;>
    simp [complexBilinearForm, coordinateBasisVector] at hzero hone <;>
    simp [inverseCoordinate, linearPolynomial, coordinateBasisVector, hzero, hone]

/-- Formal inverse coordinates evaluate to the inverse geometric action. -/
theorem inverseCoordinate_eval (n : ℕ) (element : DihedralGroup n)
    (coordinate : Fin 2) (point : ComplexPlane) :
    MvPolynomial.eval point (inverseCoordinate n element coordinate) =
      vectorOperator n element⁻¹ point coordinate := by
  conv_rhs => rw [vector_eq_coordinate_expansion point]
  simp [inverseCoordinate, map_add, map_smul]
  ring

end Schubert.Dihedral
