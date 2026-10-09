import DihedralHessenberg.Splines.ArbitraryHomogeneousBasis
import DihedralHessenberg.Splines.FinitePolynomialGrading
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraTower

/-! # Homogeneous coefficient bases of polynomial spline modules

The monomial scalar basis and a homogeneous polynomial-module basis give an infinite
coefficient basis. Restricting its degree fiber supplies a basis of a spline degree piece.
-/

noncomputable section

namespace Schubert.Splines.IdealLabeledGraph

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K P V E I : Type*} [CommRing K]
variable (graph : IdealLabeledGraph (MvPolynomial P K) V E)

/-- A polynomial spline basis yields its coefficient basis by monomial scalar expansion. -/
def polynomialSplineCoefficientBasis (basis : Module.Basis I (MvPolynomial P K) graph.Spline) :
    Module.Basis ((P →₀ ℕ) × I) K graph.Spline :=
  (MvPolynomial.basisMonomials P K).smulTower basis

/-- The coefficient basis degrees are monomial degree plus polynomial spline basis degree. -/
theorem polynomialSplineCoefficientBasis_mem
    (basis : Module.Basis I (MvPolynomial P K) graph.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ graph.homogeneousPiece (degrees index))
    (index : (P →₀ ℕ) × I) :
    graph.polynomialSplineCoefficientBasis basis index ∈
      graph.homogeneousPiece (index.1.degree + degrees index.2) := by
  rw [polynomialSplineCoefficientBasis, Module.Basis.smulTower_apply]
  intro vertex
  change ((MvPolynomial.basisMonomials P K) index.1 *
    (basis index.2 : V → MvPolynomial P K) vertex).IsHomogeneous _
  rw [MvPolynomial.coe_basisMonomials]
  exact (MvPolynomial.isHomogeneous_monomial (1 : K) rfl).mul (hbasis index.2 vertex)

variable [Fintype V]
variable (hlabels : ∀ edge,
  (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule P K))

/-- A spline degree basis consists of homogeneous monomial multiples of its module basis. -/
def polynomialSplinePieceBasis
    (basis : Module.Basis I (MvPolynomial P K) graph.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ graph.homogeneousPiece (degrees index)) (degree : ℕ) :
    Module.Basis {index : (P →₀ ℕ) × I // index.1.degree + degrees index.2 = degree} K
      (graph.homogeneousPiece degree) := by
  letI := graph.gradedAlgebra hlabels
  exact arbitraryHomogeneousPieceBasis graph.homogeneousPiece
    (graph.polynomialSplineCoefficientBasis basis)
    (fun index => index.1.degree + degrees index.2)
    (graph.polynomialSplineCoefficientBasis_mem basis degrees hbasis) degree

include hlabels in
/-- The spline degree dimension counts the shifted monomial degree fiber. -/
theorem polynomialSplinePieceBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I (MvPolynomial P K) graph.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ graph.homogeneousPiece (degrees index)) (degree : ℕ) :
    Module.finrank K (graph.homogeneousPiece degree) =
      Nat.card {index : (P →₀ ℕ) × I // index.1.degree + degrees index.2 = degree} :=
  Module.finrank_eq_nat_card_basis
    (graph.polynomialSplinePieceBasis hlabels basis degrees hbasis degree)

include hlabels in
/-- Finitely many variables and polynomial basis vectors give finite spline degree pieces. -/
theorem polynomialSplinePiece_finite [Finite P] [Finite I]
    (basis : Module.Basis I (MvPolynomial P K) graph.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ graph.homogeneousPiece (degrees index)) (degree : ℕ) :
    Module.Finite K (graph.homogeneousPiece degree) := by
  have hfinite : Set.Finite
      {index : (P →₀ ℕ) × I | index.1.degree + degrees index.2 = degree} := by
    have hproduct := (Finsupp.finite_of_degree_le (σ := P) degree).prod
      (Set.finite_univ : (Set.univ : Set I).Finite)
    apply hproduct.subset
    intro index hindex
    change index.1.degree + degrees index.2 = degree at hindex
    exact ⟨by change index.1.degree ≤ degree; omega, Set.mem_univ _⟩
  let : Finite {index : (P →₀ ℕ) × I // index.1.degree + degrees index.2 = degree} :=
    hfinite.to_subtype
  exact Module.Finite.of_basis
    (graph.polynomialSplinePieceBasis hlabels basis degrees hbasis degree)

end Schubert.Splines.IdealLabeledGraph
