import Schubert.Splines.HomogeneousBasis
import Schubert.Splines.ReflectionQuotientBasis
import Schubert.Splines.QuotientGrading

/-! # Homogeneous quotient bases from polynomial spline bases

A polynomial basis whose vectors are homogeneous descends to both quotient degree
pieces. The coefficient dimensions count the basis degrees.
-/

noncomputable section

namespace Schubert.Splines.GradedReflectionGraphData

variable {K P W T I : Type*} [CommRing K] [Group W]
variable (data : GradedReflectionGraphData K P W T) (selected : Set T)

/-- A left quotient basis vector retains its polynomial spline degree. -/
theorem leftQuotientBasis_mem_homogeneousPiece
    (basis : Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index))
    (index : I) :
    data.toReflectionGraphData.leftQuotientBasis selected basis index ∈
      data.leftQuotientPiece selected (degrees index) := by
  rw [ReflectionGraphData.leftQuotientBasis_apply]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.leftVariableIdeal selected) (hbasis index)

/-- A right quotient basis vector retains its polynomial spline degree. -/
theorem rightQuotientBasis_mem_homogeneousPiece
    (basis : letI := data.toReflectionGraphData.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index))
    (index : I) :
    data.toReflectionGraphData.rightQuotientBasis selected basis index ∈
      data.rightQuotientPiece selected (degrees index) := by
  rw [ReflectionGraphData.rightQuotientBasis_apply]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.rightVariableIdeal selected) (hbasis index)

variable [Fintype W] [Fintype I]

/-- Restrict the left quotient basis to the classes of one degree. -/
def leftQuotientPieceBasis
    (basis : Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index)) (degree : ℕ) :
    Module.Basis {index // degrees index = degree} K (data.leftQuotientPiece selected degree) := by
  letI := data.leftQuotientGradedAlgebra selected
  exact homogeneousPieceBasis (data.leftQuotientPiece selected)
    (data.toReflectionGraphData.leftQuotientBasis selected basis) degrees
    (data.leftQuotientBasis_mem_homogeneousPiece selected basis degrees hbasis) degree

/-- Restrict the right quotient basis to the classes of one degree. -/
def rightQuotientPieceBasis
    (basis : letI := data.toReflectionGraphData.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index)) (degree : ℕ) :
    Module.Basis {index // degrees index = degree} K (data.rightQuotientPiece selected degree) := by
  letI := data.rightQuotientGradedAlgebra selected
  exact homogeneousPieceBasis (data.rightQuotientPiece selected)
    (data.toReflectionGraphData.rightQuotientBasis selected basis) degrees
    (data.rightQuotientBasis_mem_homogeneousPiece selected basis degrees hbasis) degree

/-- The left quotient degree dimension is its homogeneous polynomial-basis degree count. -/
theorem leftQuotientPieceBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index)) (degree : ℕ) :
    Module.finrank K (data.leftQuotientPiece selected degree) =
      Nat.card {index // degrees index = degree} :=
  Module.finrank_eq_nat_card_basis
    (data.leftQuotientPieceBasis selected basis degrees hbasis degree)

/-- The right quotient degree dimension is its homogeneous polynomial-basis degree count. -/
theorem rightQuotientPieceBasis_finrank [StrongRankCondition K]
    (basis : letI := data.toReflectionGraphData.rightAlgebra selected
      Module.Basis I (MvPolynomial P K) (data.toReflectionGraphData.Spline selected))
    (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ data.homogeneousPiece selected (degrees index)) (degree : ℕ) :
    Module.finrank K (data.rightQuotientPiece selected degree) =
      Nat.card {index // degrees index = degree} :=
  Module.finrank_eq_nat_card_basis
    (data.rightQuotientPieceBasis selected basis degrees hbasis degree)

end Schubert.Splines.GradedReflectionGraphData
