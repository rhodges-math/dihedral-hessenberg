import DihedralHessenberg.Splines.PolynomialSplinePieceBasis
import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.Analysis.Complex.Basic

/-! # Coefficient convolution for a homogeneous polynomial spline basis -/

noncomputable section

namespace Schubert.Splines

/-- Shifted binary monomials have the expected nonnegative degree count. -/
theorem card_binary_monomial_shift (shift degree : ℕ) :
    Nat.card {index : Fin 2 →₀ ℕ // index.degree + shift = degree} =
      if shift ≤ degree then degree - shift + 1 else 0 := by
  classical
  by_cases hle : shift ≤ degree
  · rw [ite_eq_left hle]
    let equiv : {index : Fin 2 →₀ ℕ // index.degree + shift = degree} ≃
        {index : Fin 2 →₀ ℕ // index.degree = degree - shift} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun index => by simp only [Equiv.refl_apply]; omega)
    rw [Nat.card_congr equiv]
    change Nat.card (↥{index : Fin 2 →₀ ℕ | index.degree = degree - shift}) = _
    rw [← TauCeti.finrank_homogeneousSubmodule
      (Fin 2) ℂ, TauCeti.finrank_homogeneousSubmodule_fin_two]
  · rw [ite_eq_right hle]
    let : IsEmpty {index : Fin 2 →₀ ℕ // index.degree + shift = degree} :=
      ⟨fun index => by have h := index.property; omega⟩
    simp

namespace IdealLabeledGraph

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V E I : Type*} [Fintype V] [Fintype I]
variable (graph : IdealLabeledGraph (MvPolynomial (Fin 2) ℂ) V E)

/-- A binary polynomial spline basis gives the explicit Hilbert coefficient convolution. -/
theorem _root_.Schubert.Splines.IdealLabeledGraph.piece_finrank_convolution
    (hlabels : ∀ edge,
      (graph.label edge).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ))
    (basis : Module.Basis I (MvPolynomial (Fin 2) ℂ) graph.Spline) (degrees : I → ℕ)
    (hbasis : ∀ index, basis index ∈ graph.homogeneousPiece (degrees index)) (degree : ℕ) :
    Module.finrank ℂ (graph.homogeneousPiece degree) =
      ∑ index, if degrees index ≤ degree then degree - degrees index + 1 else 0 := by
  classical
  let equiv : {index : (Fin 2 →₀ ℕ) × I // index.1.degree + degrees index.2 = degree} ≃
      Σ index : I, {monomial : Fin 2 →₀ ℕ // monomial.degree + degrees index = degree} := {
    toFun := fun index => ⟨index.val.2, ⟨index.val.1, index.property⟩⟩
    invFun := fun index => ⟨(index.2.val, index.1), index.2.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : ∀ index : I, Finite
      {monomial : Fin 2 →₀ ℕ // monomial.degree + degrees index = degree} := fun index => by
    have hfinite := (Finsupp.finite_of_degree_le (σ := Fin 2) degree).subset
      (show {monomial : Fin 2 →₀ ℕ | monomial.degree + degrees index = degree} ⊆
        {monomial : Fin 2 →₀ ℕ | monomial.degree ≤ degree} from fun monomial h => by
          change monomial.degree + degrees index = degree at h
          change monomial.degree ≤ degree
          omega)
    exact hfinite.to_subtype
  rw [graph.polynomialSplinePieceBasis_finrank hlabels basis degrees hbasis,
    Nat.card_congr equiv, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun index _ => card_binary_monomial_shift (degrees index) degree)

end IdealLabeledGraph

end Schubert.Splines
