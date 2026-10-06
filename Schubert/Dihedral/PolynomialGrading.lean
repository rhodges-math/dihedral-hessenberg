import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Schubert.Dihedral.RotationAction

/-! # Homogeneity of dihedral polynomial substitutions

Linear forms are homogeneous of degree one, and substitution by a linear operator
preserves polynomial homogeneous degree. In particular, the dihedral coefficient
action preserves every degree piece of the polynomial ring.
-/

namespace Schubert.Dihedral

/-- The polynomial associated to a vector is homogeneous of degree one. -/
theorem linearPolynomial_isHomogeneous (vector : ComplexPlane) :
    (linearPolynomial vector).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_C_mul_X (vector 0) (0 : Fin 2)).add
    (MvPolynomial.isHomogeneous_C_mul_X (vector 1) (1 : Fin 2))

/-- Substitution by a linear operator preserves each homogeneous polynomial degree. -/
theorem polynomialSubstitution_isHomogeneous (operator : ComplexPlane →ₗ[ℂ] ComplexPlane)
    {degree : ℕ} {polynomial : CoordinatePolynomial}
    (hpolynomial : polynomial.IsHomogeneous degree) :
    (polynomialSubstitution operator polynomial).IsHomogeneous degree := by
  simpa only [one_mul, polynomialSubstitution] using
    hpolynomial.aeval
      (fun coordinate => linearPolynomial (operator (coordinateBasisVector coordinate)))
      (fun coordinate =>
        linearPolynomial_isHomogeneous (operator (coordinateBasisVector coordinate)))

/-- Every dihedral polynomial automorphism preserves homogeneous degree. -/
theorem polynomialAction_isHomogeneous (n : ℕ) [NeZero n] (element : DihedralGroup n)
    {degree : ℕ} {polynomial : CoordinatePolynomial}
    (hpolynomial : polynomial.IsHomogeneous degree) :
    (polynomialAction n element polynomial).IsHomogeneous degree :=
  polynomialSubstitution_isHomogeneous (vectorOperator n element) hpolynomial

/-- Every root label is homogeneous of degree one. -/
theorem rootPolynomial_isHomogeneous (n : ℕ) (index : PositiveRootIndex n) :
    (rootPolynomial n index).IsHomogeneous 1 :=
  linearPolynomial_isHomogeneous (complexPositiveRoot n index)

end Schubert.Dihedral
