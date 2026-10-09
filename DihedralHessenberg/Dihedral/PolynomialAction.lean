import DihedralHessenberg.Dihedral.RealizationBasic

/-!
# Polynomial substitution from coordinate linear operators

The map from vectors to linear polynomials intertwines linear operators with their induced
polynomial substitutions. This construction preserves identity and composition.
-/

noncomputable section

namespace Schubert.Dihedral

theorem coordinateBasisVector_zero : coordinateBasisVector 0 = ![(1 : ℂ), 0] := by
  apply complexPlane_ext <;> simp [coordinateBasisVector]

theorem coordinateBasisVector_one : coordinateBasisVector 1 = ![(0 : ℂ), 1] := by
  apply complexPlane_ext <;> simp [coordinateBasisVector]

/-- Every vector is the linear combination of its coordinate basis vectors. -/
theorem vector_eq_coordinate_expansion (vector : ComplexPlane) :
    vector = vector 0 • coordinateBasisVector 0 + vector 1 • coordinateBasisVector 1 := by
  apply complexPlane_ext <;> simp [coordinateBasisVector]

theorem linearPolynomial_add (first second : ComplexPlane) :
    linearPolynomial (first + second) = linearPolynomial first + linearPolynomial second := by
  simp only [linearPolynomial, Pi.add_apply, map_add]
  ring

theorem linearPolynomial_smul (scalar : ℂ) (vector : ComplexPlane) :
    linearPolynomial (scalar • vector) = MvPolynomial.C scalar * linearPolynomial vector := by
  simp only [linearPolynomial, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem linearPolynomial_basis (coordinate : Fin 2) :
    linearPolynomial (coordinateBasisVector coordinate) = MvPolynomial.X coordinate := by
  fin_cases coordinate <;> simp [linearPolynomial, coordinateBasisVector]

/-- Evaluating the polynomial of a vector is bilinear pairing with the evaluation point. -/
theorem linearPolynomial_eval (vector point : ComplexPlane) :
    MvPolynomial.eval point (linearPolynomial vector) = complexBilinearForm vector point := by
  simp [linearPolynomial, complexBilinearForm]

/-- Polynomial substitution sends the polynomial of a vector to that of its image. -/
theorem polynomialSubstitution_linearPolynomial (operator : ComplexPlane →ₗ[ℂ] ComplexPlane)
    (vector : ComplexPlane) :
    polynomialSubstitution operator (linearPolynomial vector) =
      linearPolynomial (operator vector) := by
  conv_rhs => rw [vector_eq_coordinate_expansion vector]
  simp [linearPolynomial, map_add, map_smul, polynomialSubstitution_variable]
  ring

/-- The identity linear operator induces identity polynomial substitution. -/
theorem polynomialSubstitution_id :
    polynomialSubstitution LinearMap.id = AlgHom.id ℂ CoordinatePolynomial := by
  ext coordinate : 1
  rw [polynomialSubstitution_variable]
  exact linearPolynomial_basis coordinate

/-- Composition of linear operators agrees with composition of polynomial substitutions. -/
theorem polynomialSubstitution_comp (first second : ComplexPlane →ₗ[ℂ] ComplexPlane) :
    polynomialSubstitution (first.comp second) =
      (polynomialSubstitution first).comp (polynomialSubstitution second) := by
  ext coordinate : 1
  simp only [polynomialSubstitution_variable, AlgHom.comp_apply, LinearMap.comp_apply,
    polynomialSubstitution_linearPolynomial]

end Schubert.Dihedral
