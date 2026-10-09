import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import DihedralHessenberg.Splines.ArbitraryHomogeneousBasis
import Lean.Elab.Tactic.Omega

/-! # Homogeneous coordinates in polynomial module bases -/

noncomputable section

namespace Schubert.Splines

variable {K P M I : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable [Module (MvPolynomial P K) M] [IsScalarTower K (MvPolynomial P K) M]
variable (pieces : ℕ → Submodule K M) [DirectSum.Decomposition pieces]
variable (basis : Module.Basis I (MvPolynomial P K) M) (weights : I → ℕ)
variable (hbasis : ∀ index, basis index ∈ pieces (weights index))
variable (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : M),
  polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
    polynomial • value ∈ pieces (scalarDegree + valueDegree))

include hbasis hsmul

/-- A homogeneous vector has no polynomial basis coordinate outside its weighted total degree. -/
theorem polynomial_basis_coeff_zero (degree : ℕ) {value : M} (hvalue : value ∈ pieces degree)
    (index : I) (exponent : P →₀ ℕ) (hne : exponent.degree + weights index ≠ degree) :
    (basis.repr value index).coeff exponent = 0 := by
  let tower := (MvPolynomial.basisMonomials P K).smulTower basis
  have htower : ∀ pair, tower pair ∈ pieces (pair.1.degree + weights pair.2) := by
    intro pair
    rw [Module.Basis.smulTower_apply]
    exact hsmul _ _ _ _ (MvPolynomial.isHomogeneous_monomial _ rfl) (hbasis pair.2)
  have hzero := HomogeneousBasis.repr_zero_of_degree_ne pieces tower
    (fun pair => pair.1.degree + weights pair.2) htower degree hvalue (exponent, index) hne
  rw [Module.Basis.smulTower_repr] at hzero
  exact hzero

/-- Coordinates at equal or higher basis weights are constants in a homogeneous vector. -/
theorem polynomial_basis_repr_constant (degree : ℕ) {value : M} (hvalue : value ∈ pieces degree)
    (index : I) (hle : degree ≤ weights index) :
    basis.repr value index = MvPolynomial.C (basis.repr value index).constantCoeff := by
  classical
  apply MvPolynomial.ext
  intro exponent
  by_cases hzero : exponent = 0
  · subst exponent
    simp [MvPolynomial.constantCoeff_eq]
  · have hpositive : 0 < exponent.degree := by
      apply Nat.pos_of_ne_zero
      intro hdegree
      exact hzero ((Finsupp.degree_eq_zero_iff exponent).mp hdegree)
    rw [MvPolynomial.coeff_C, ite_eq_right (Ne.symm hzero)]
    exact polynomial_basis_coeff_zero pieces basis weights hbasis hsmul degree hvalue index
      exponent (by omega)

end Schubert.Splines
