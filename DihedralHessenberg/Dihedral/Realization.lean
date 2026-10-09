import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Pi
import DihedralHessenberg.Dihedral.Group

/-!
# The planar realization of the dihedral group

This file defines unit roots in the real plane, their complexification, the symmetric bilinear
form, and the corresponding linear polynomials. Polynomial substitution sends a variable to
the polynomial associated to the image of its basis vector.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The real coordinate plane. -/
abbrev RealPlane := Fin 2 → ℝ

/-- The complex coordinate plane. -/
abbrev ComplexPlane := Fin 2 → ℂ

/-- The polynomial algebra in the two coordinate variables. -/
abbrev CoordinatePolynomial := MvPolynomial (Fin 2) ℂ

/-- The standard symmetric bilinear form on the real plane. -/
def realBilinearForm (first second : RealPlane) : ℝ :=
  first 0 * second 0 + first 1 * second 1

/-- The complex bilinear extension of the standard real form, without conjugation. -/
def complexBilinearForm (first second : ComplexPlane) : ℂ :=
  first 0 * second 0 + first 1 * second 1

/-- Coordinatewise inclusion of the real plane in the complex plane. -/
def complexify (vector : RealPlane) : ComplexPlane :=
  fun coordinate => (vector coordinate : ℂ)

/-- The unit vector at the given angle, measured counterclockwise from the first coordinate. -/
def unitRootAt (angle : ℝ) : RealPlane :=
  ![Real.cos angle, Real.sin angle]

/-- The angle of a positive root, where index `i` denotes the root numbered `i.val + 1`. -/
def rootAngle (n : ℕ) (index : PositiveRootIndex n) : ℝ :=
  if index.val % 2 = 0 then
    (index.val / 2 : ℕ) * Real.pi / n
  else
    (n - 1 - index.val / 2 : ℕ) * Real.pi / n

/-- The positive unit root with the alternating reflection indexing. -/
def positiveRoot (n : ℕ) (index : PositiveRootIndex n) : RealPlane :=
  unitRootAt (rootAngle n index)

/-- The set of positive roots in the real plane. -/
def positiveRoots (n : ℕ) : Set RealPlane :=
  Set.range (positiveRoot n)

/-- The complete real root set, including both signs of each positive root. -/
def roots (n : ℕ) : Set RealPlane :=
  positiveRoots n ∪ {vector | -vector ∈ positiveRoots n}

/-- The positive root viewed in the complex coordinate plane. -/
def complexPositiveRoot (n : ℕ) (index : PositiveRootIndex n) : ComplexPlane :=
  complexify (positiveRoot n index)

/-- The linear functional pairing a vector with a fixed vector under the complex bilinear form. -/
def complexPairing (normal : ComplexPlane) : ComplexPlane →ₗ[ℂ] ℂ :=
  normal 0 • LinearMap.proj 0 + normal 1 • LinearMap.proj 1

/-- Reflection across the orthogonal hyperplane of a nonisotropic complex normal vector. -/
def complexReflection (normal : ComplexPlane) : ComplexPlane →ₗ[ℂ] ComplexPlane :=
  LinearMap.id - (2 / complexBilinearForm normal normal) •
    (complexPairing normal).smulRight normal

/-- Counterclockwise rotation of the complexified real plane by a real angle. -/
def complexRotation (angle : ℝ) : ComplexPlane →ₗ[ℂ] ComplexPlane :=
  LinearMap.pi ![
    (Real.cos angle : ℂ) • LinearMap.proj 0 -
      (Real.sin angle : ℂ) • LinearMap.proj 1,
    (Real.sin angle : ℂ) • LinearMap.proj 0 +
      (Real.cos angle : ℂ) • LinearMap.proj 1]

/-- The coordinate linear operator assigned to a dihedral rotation or reflection. -/
def vectorOperator (n : ℕ) : DihedralGroup n → ComplexPlane →ₗ[ℂ] ComplexPlane
  | .r exponent => complexRotation (2 * Real.pi * exponent.val / n)
  | .sr exponent =>
    complexReflection (complexify (unitRootAt (-Real.pi * exponent.val / n)))

/-- The linear polynomial associated to a complex vector by mapping basis vectors to variables. -/
def linearPolynomial (vector : ComplexPlane) : CoordinatePolynomial :=
  MvPolynomial.C (vector 0) * MvPolynomial.X 0 +
    MvPolynomial.C (vector 1) * MvPolynomial.X 1

/-- The linear polynomial associated to a positive unit root. -/
def rootPolynomial (n : ℕ) (index : PositiveRootIndex n) : CoordinatePolynomial :=
  linearPolynomial (complexPositiveRoot n index)

/-- The standard coordinate basis vector. -/
def coordinateBasisVector (coordinate : Fin 2) : ComplexPlane :=
  Pi.single coordinate 1

/-- Polynomial substitution induced by the images of coordinate basis vectors. -/
def polynomialSubstitution (operator : ComplexPlane →ₗ[ℂ] ComplexPlane) :
    CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial :=
  MvPolynomial.aeval (fun coordinate =>
    linearPolynomial (operator (coordinateBasisVector coordinate)))

/-- Polynomial substitution assigned to a dihedral element through its coordinate operator. -/
def polynomialOperator (n : ℕ) (element : DihedralGroup n) :
    CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial :=
  polynomialSubstitution (vectorOperator n element)

/-- A trigonometric unit vector has squared length one under the real bilinear form. -/
theorem realBilinearForm_unitRootAt (angle : ℝ) :
    realBilinearForm (unitRootAt angle) (unitRootAt angle) = 1 := by
  simpa only [realBilinearForm, unitRootAt, Matrix.cons_val_zero, Matrix.cons_val_one,
    pow_two] using Real.cos_sq_add_sin_sq angle

/-- Every indexed positive root has squared length one. -/
theorem positiveRoot_unit (n : ℕ) (index : PositiveRootIndex n) :
    realBilinearForm (positiveRoot n index) (positiveRoot n index) = 1 :=
  realBilinearForm_unitRootAt (rootAngle n index)

/-- Substitution sends each coordinate variable to the polynomial of its basis-vector image. -/
theorem polynomialSubstitution_variable (operator : ComplexPlane →ₗ[ℂ] ComplexPlane)
    (coordinate : Fin 2) :
    polynomialSubstitution operator (MvPolynomial.X coordinate) =
      linearPolynomial (operator (coordinateBasisVector coordinate)) :=
  MvPolynomial.aeval_X _ coordinate

end Schubert.Dihedral
