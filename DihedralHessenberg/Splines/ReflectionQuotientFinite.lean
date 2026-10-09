import DihedralHessenberg.Splines.QuotientFinite
import DihedralHessenberg.Splines.Quotient

/-! # Finite polynomial-basis reflection spline quotients

Both scalar structures give finite coefficient modules after their own
coordinate scalars vanish. A finite polynomial basis is an explicit hypothesis.
-/

namespace Schubert.Splines.ReflectionGraphData

variable {K P W T I : Type*} [CommRing K] [Group W] [Fintype I]
variable (data : ReflectionGraphData K (MvPolynomial P K) W T) (selected : Set T)

/-- A finite left polynomial basis makes the left quotient finite over coefficients. -/
theorem leftQuotient_finite_of_basis
    (basis : Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.Finite K (data.LeftQuotient selected) := by
  exact quotient_finite_of_variables_zero (K := K) (P := P)
    (A := data.Spline selected) (B := data.LeftQuotient selected)
    basis (data.leftQuotientMap selected)
    (data.leftQuotientMap_surjective selected) (by
      intro coordinate
      change data.leftQuotientMap selected
        (data.constantSpline selected (MvPolynomial.X coordinate)) = 0
      exact data.leftQuotientMap_coordinate selected coordinate)

/-- A finite right polynomial basis makes the right quotient finite over coefficients. -/
theorem rightQuotient_finite_of_basis
    (basis : letI := data.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.Finite K (data.RightQuotient selected) := by
  let := data.rightAlgebra selected
  exact quotient_finite_of_variables_zero (K := K) (P := P)
    (A := data.Spline selected) (B := data.RightQuotient selected)
    basis (data.rightQuotientMap selected)
    (data.rightQuotientMap_surjective selected) (by
      intro coordinate
      change data.rightQuotientMap selected
        (data.orbitSpline selected (MvPolynomial.X coordinate)) = 0
      exact data.rightQuotientMap_coordinate selected coordinate)

end Schubert.Splines.ReflectionGraphData
