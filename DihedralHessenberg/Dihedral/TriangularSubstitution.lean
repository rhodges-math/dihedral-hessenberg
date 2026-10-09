import DihedralHessenberg.Dihedral.PolynomialAction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Coordinate substitution by a concrete triangular operator -/

noncomputable section

namespace Schubert.Dihedral

/-- The coordinate basis images are the columns of the triangular matrix. -/
theorem triangular_basis_images :
    Matrix.toLin' !![(-1 : ℂ), 1; 0, 2] (coordinateBasisVector 0) = ![-1, 0] ∧
      Matrix.toLin' !![(-1 : ℂ), 1; 0, 2] (coordinateBasisVector 1) = ![1, 2] := by
  constructor <;> funext coordinate <;> fin_cases coordinate <;>
    simp [Matrix.toLin'_apply, coordinateBasisVector_zero, coordinateBasisVector_one]

/-- The triangular substitution negates the first polynomial coordinate. -/
theorem triangular_first_variable :
    polynomialSubstitution (Matrix.toLin' !![(-1 : ℂ), 1; 0, 2])
      (MvPolynomial.X (0 : Fin 2)) = -MvPolynomial.X 0 := by
  rw [polynomialSubstitution_variable, triangular_basis_images.1]
  simp [linearPolynomial]

/-- The second column gives the second substituted polynomial coordinate. -/
theorem triangular_second_variable :
    polynomialSubstitution (Matrix.toLin' !![(-1 : ℂ), 1; 0, 2])
      (MvPolynomial.X (1 : Fin 2)) =
        MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.X 1 := by
  rw [polynomialSubstitution_variable, triangular_basis_images.2]
  simp [linearPolynomial]

/-- Coordinate substitution acts multiplicatively on a mixed cubic monomial. -/
theorem triangular_monomial :
    polynomialSubstitution (Matrix.toLin' !![(-1 : ℂ), 1; 0, 2])
      (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1 ^ 2) =
        -MvPolynomial.X 0 * (MvPolynomial.X 0 + MvPolynomial.C 2 * MvPolynomial.X 1) ^ 2 := by
  rw [map_mul, map_pow, triangular_first_variable, triangular_second_variable]

/-- Coordinate substitution acts linearly on the sum of the two variables. -/
theorem triangular_sum :
    polynomialSubstitution (Matrix.toLin' !![(-1 : ℂ), 1; 0, 2])
      (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X 1) =
        MvPolynomial.C 2 * MvPolynomial.X 1 := by
  rw [map_add, triangular_first_variable, triangular_second_variable]
  ring

end Schubert.Dihedral
