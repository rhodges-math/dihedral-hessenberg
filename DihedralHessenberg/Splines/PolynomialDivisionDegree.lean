import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Lean.Elab.Tactic.Omega

/-! # Degree bounds for exact polynomial division

The multiplied numerator equation gives a total-degree bound on its quotient.
No choice of a division algorithm or spline operator is required.
-/

namespace Schubert.Splines

variable {K P : Type*} [CommRing K] [IsDomain K]

/-- Exact division by a nonzero polynomial lowers the degree bound by its degree. -/
theorem polynomial_quotient_totalDegree_le
    {label numerator quotient : MvPolynomial P K} {degree : ℕ}
    (hlabel : label ≠ 0) (hquotient : label * quotient = numerator)
    (hdegree : numerator.totalDegree ≤ degree) :
    quotient.totalDegree ≤ degree - label.totalDegree := by
  by_cases hzero : quotient = 0
  · subst quotient
    simp
  · rw [← hquotient, MvPolynomial.totalDegree_mul_of_isDomain hlabel hzero] at hdegree
    omega

/-- A linear nonzero divisor lowers the numerator degree bound by one. -/
theorem _root_.Schubert.Splines.PolynomialDivisionDegree.linear_quotient_degree_le
    {label numerator quotient : MvPolynomial P K} {degree : ℕ}
    (hlabel : label ≠ 0) (hlinear : label.totalDegree = 1)
    (hquotient : label * quotient = numerator) (hdegree : numerator.totalDegree ≤ degree) :
    quotient.totalDegree ≤ degree - 1 := by
  simpa only [hlinear] using polynomial_quotient_totalDegree_le hlabel hquotient hdegree

end Schubert.Splines
