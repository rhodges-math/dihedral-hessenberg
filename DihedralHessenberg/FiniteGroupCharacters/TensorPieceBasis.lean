import DihedralHessenberg.FiniteGroupCharacters.TensorGrading
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Degree fibers of ordinary homogeneous tensor bases -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

/-- The ordinary tensor degree is the span of the total-degree monomial basis fiber. -/
theorem tensor_piece_span {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    tensorPiece (P := P) pieces degree = Submodule.span K
      (Set.range fun index : {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree} =>
        ((MvPolynomial.basisMonomials P K).tensorProduct basis) index.val) := by
  classical
  let tower := (MvPolynomial.basisMonomials P K).tensorProduct basis
  have hzero : ∀ (value : MvPolynomial P K ⊗[K] Q), value ∈ tensorPiece pieces degree →
      ∀ pair, pair.1.degree + weights pair.2 ≠ degree → tower.repr value pair = 0 := by
    intro value hvalue pair hne
    induction hvalue using Submodule.span_induction with
    | mem value hvalue =>
        obtain ⟨scalarDegree, valueDegree, polynomial, vector, hdegree, hpoly, hvector, rfl⟩ :=
          hvalue
        rw [Module.Basis.tensorProduct_repr_tmul_apply]
        by_cases heq : weights pair.2 = valueDegree
        · have hpolyne : pair.1.degree ≠ scalarDegree := by omega
          change _ • polynomial.coeff pair.1 = 0
          rw [hpoly.coeff_eq_zero hpolyne, smul_zero]
        · rw [Schubert.Splines.HomogeneousBasis.repr_zero_of_degree_ne
            pieces basis weights hbasis valueDegree hvector pair.2 heq, zero_smul]
    | zero => simp
    | add value other _ _ hvalue hother => simp [hvalue, hother]
    | smul scalar value _ hvalue => simp [hvalue]
  apply le_antisymm
  · intro value hvalue
    rw [← tower.linearCombination_repr value, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro pair _
    by_cases heq : pair.1.degree + weights pair.2 = degree
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨pair, heq⟩, rfl⟩)
    · rw [hzero value hvalue pair heq, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    change ((MvPolynomial.basisMonomials P K).tensorProduct basis) index.val ∈ _
    rw [Module.Basis.tensorProduct_apply']
    exact Submodule.subset_span ⟨index.val.1.degree, weights index.val.2,
      MvPolynomial.monomial index.val.1 1, basis index.val.2, index.property,
      MvPolynomial.isHomogeneous_monomial _ rfl, hbasis index.val.2, rfl⟩

/-- The total-degree fiber gives a basis of the ordinary tensor piece. -/
def tensorPieceBasis {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ) :
    Module.Basis {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree} K
      (tensorPiece (P := P) pieces degree) :=
  (Module.Basis.span (((MvPolynomial.basisMonomials P K).tensorProduct basis).linearIndependent.comp
    Subtype.val Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (tensor_piece_span pieces basis weights hbasis degree).symm)

/-- The restricted degree basis is its pure monomial tensor. -/
theorem tensorPieceBasis_apply {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (index : {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree}) :
    (tensorPieceBasis (P := P) pieces basis weights hbasis degree index).val =
      MvPolynomial.monomial index.val.1 1 ⊗ₜ[K] basis index.val.2 := by
  simp [tensorPieceBasis, Module.Basis.tensorProduct_apply']

/-- Restricted tensor coordinates agree with the ambient tensor coordinates at their index. -/
theorem tensorPieceBasis_repr {K P Q I : Type*} [CommRing K]
    [AddCommGroup Q] [Module K Q] (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index)) (degree : ℕ)
    (value : tensorPiece (P := P) pieces degree)
    (index : {pair : (P →₀ ℕ) × I // pair.1.degree + weights pair.2 = degree}) :
    (tensorPieceBasis pieces basis weights hbasis degree).repr value index =
      ((MvPolynomial.basisMonomials P K).tensorProduct basis).repr value.val index.val := by
  classical
  let restricted := tensorPieceBasis (P := P) pieces basis weights hbasis degree
  let tower := (MvPolynomial.basisMonomials P K).tensorProduct basis
  have hcoord : restricted.coord index =
      (tower.coord index.val).comp (tensorPiece (P := P) pieces degree).subtype := by
    apply restricted.ext
    intro other
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply]
    have hvalue : (tensorPiece (P := P) pieces degree).subtype (restricted other) =
        tower other.val := by
      change (tensorPieceBasis pieces basis weights hbasis degree other).val = _
      rw [tensorPieceBasis_apply]
      exact (Module.Basis.tensorProduct_apply' _ _ _).symm
    rw [hvalue]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, ← Subtype.ext_iff]
  exact LinearMap.congr_fun hcoord value

end Schubert.FiniteGroupCharacters
