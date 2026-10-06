import Schubert.Splines.GraphFinite
import Schubert.Splines.FinitePolynomialQuotient
import Schubert.Splines.Quotient
import Mathlib.RingTheory.Polynomial.Basic

/-! # Finite coefficient quotients of polynomial reflection splines -/

namespace Schubert.Splines.ReflectionGraphData

variable {K P W T : Type*} [CommRing K] [IsNoetherianRing K]
variable [Finite P] [Group W] [Fintype W]
variable (data : ReflectionGraphData K (MvPolynomial P K) W T) (selected : Set T)

/-- The whole left quotient is finite without a polynomial basis hypothesis. -/
theorem leftQuotient_finite : Module.Finite K (data.LeftQuotient selected) := by
  let := data.leftSpline_finite selected
  exact _root_.Schubert.Splines.QuotientFinite.finite_of_X_zero (K := K) (P := P)
    (A := data.Spline selected) (B := data.LeftQuotient selected)
    (data.leftQuotientMap selected) (data.leftQuotientMap_surjective selected) (by
      intro coordinate
      change data.leftQuotientMap selected
        (data.constantSpline selected (MvPolynomial.X coordinate)) = 0
      exact data.leftQuotientMap_coordinate selected coordinate)

/-- The whole right quotient is finite without a polynomial basis hypothesis. -/
theorem rightQuotient_finite : Module.Finite K (data.RightQuotient selected) := by
  let := data.rightAlgebra selected
  let := data.rightSpline_finite selected
  exact _root_.Schubert.Splines.QuotientFinite.finite_of_X_zero (K := K) (P := P)
    (A := data.Spline selected) (B := data.RightQuotient selected)
    (data.rightQuotientMap selected) (data.rightQuotientMap_surjective selected) (by
      intro coordinate
      change data.rightQuotientMap selected
        (data.orbitSpline selected (MvPolynomial.X coordinate)) = 0
      exact data.rightQuotientMap_coordinate selected coordinate)

end Schubert.Splines.ReflectionGraphData
