import Schubert.FiniteGroupCharacters.TensorPieceBasis
import TauCeti.RingTheory.MvPolynomial.Finrank
import Mathlib.Data.Fintype.Sigma

/-! # Finiteness of ordinary tensor homogeneous components -/

noncomputable section
namespace Schubert.FiniteGroupCharacters

/-- The total-degree index fiber is finite with finitely many variables and quotient indices. -/
theorem tensor_degree_fiber_finite {K P I : Type*} [Field K] [Finite P] [Finite I]
    (weights : I → ℕ) (degree : ℕ) :
    Finite {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree} := by
  classical
  let exponents : I → Type _ := fun index =>
    {exponent : P →₀ ℕ // exponent.degree = degree - weights index}
  let : Fintype I := Fintype.ofFinite I
  let : ∀ index, Fintype (exponents index) := fun index =>
    FiniteDimensional.fintypeBasisIndex
      (TauCeti.homogeneousMonomialBasis (R := K) (degree - weights index))
  let embed : {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree} →
      Sigma exponents := fun pair => ⟨pair.val.2, ⟨pair.val.1, by
        have hdegree := pair.property
        omega⟩⟩
  apply Finite.of_injective embed
  intro first second hequal
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun value : Sigma exponents => value.2.val) hequal
  · exact congrArg Sigma.fst hequal

/-- The ordinary tensor degree is finite for a finite homogeneous quotient basis. -/
theorem tensor_piece_finite {K P Q I : Type*} [Field K] [Finite P] [Finite I]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    Module.Finite K (tensorPiece (P := P) pieces degree) := by
  let := tensor_degree_fiber_finite (K := K) (P := P) weights degree
  exact Module.Finite.of_basis (tensorPieceBasis pieces basis weights hbasis degree)

end Schubert.FiniteGroupCharacters
