import DihedralHessenberg.Splines.PolynomialAlgebraQuotientBasis
import DihedralHessenberg.Splines.Quotient

/-! # Descending both polynomial scalar bases of reflection splines

The left quotient uses constant scalar extension and the right quotient uses
orbit scalar extension. Each explicit polynomial basis descends to the corresponding
coefficient-ring quotient basis, with its basis vector classes.
-/

noncomputable section

namespace Schubert.Splines.ReflectionGraphData

variable {K P W T I : Type*} [CommRing K] [Group W]
variable (data : ReflectionGraphData K (MvPolynomial P K) W T) (selected : Set T)

/-- Descend a constant-scalar polynomial basis to the left spline quotient. -/
def leftQuotientBasis (basis : Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.Basis I K (data.LeftQuotient selected) :=
  polynomialAlgebraQuotientBasis basis

/-- Descend an orbit-scalar polynomial basis to the right spline quotient. -/
def rightQuotientBasis
    (basis : letI := data.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.Basis I K (data.RightQuotient selected) := by
  letI := data.rightAlgebra selected
  exact polynomialAlgebraQuotientBasis basis

/-- A left quotient basis vector is its basis vector class. -/
theorem leftQuotientBasis_apply
    (basis : Module.Basis I (MvPolynomial P K) (data.Spline selected)) (index : I) :
    data.leftQuotientBasis selected basis index = data.leftQuotientMap selected (basis index) :=
  polynomialAlgebraQuotientBasis_apply basis index

/-- A right quotient basis vector is its basis vector class. -/
theorem rightQuotientBasis_apply
    (basis : letI := data.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.Spline selected)) (index : I) :
    data.rightQuotientBasis selected basis index =
      data.rightQuotientMap selected (basis index) := by
  let := data.rightAlgebra selected
  exact polynomialAlgebraQuotientBasis_apply basis index

/-- The left quotient coefficient rank equals the polynomial basis cardinality. -/
theorem leftQuotientBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.finrank K (data.LeftQuotient selected) = Nat.card I :=
  Module.finrank_eq_nat_card_basis (data.leftQuotientBasis selected basis)

/-- The right quotient coefficient rank equals the polynomial basis cardinality. -/
theorem rightQuotientBasis_finrank [StrongRankCondition K]
    (basis : letI := data.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.Spline selected)) :
    Module.finrank K (data.RightQuotient selected) = Nat.card I :=
  Module.finrank_eq_nat_card_basis (data.rightQuotientBasis selected basis)

end Schubert.Splines.ReflectionGraphData
