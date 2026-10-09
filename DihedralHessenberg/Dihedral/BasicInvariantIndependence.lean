import DihedralHessenberg.Dihedral.InvariantIndependence

/-! # Algebraic independence of the basic dihedral invariants

Distinct leading degrees of invariant monomials make their evaluation map injective.
The auxiliary coordinate equivalence transfers this statement to uv and the signed
degree-n power sum in the official polynomial algebra.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A monomial in the auxiliary invariant generators has its explicit leading degree. -/
theorem _root_.Schubert.Dihedral.Invariants.monomial_leading_degree (n : ℕ) (hpositive : 0 < n)
    (exponent : Fin 2 →₀ ℕ) :
    (MonomialOrder.lex (σ := Fin 2)).degree
      (MvPolynomial.aeval (fun coordinate : Fin 2 => if coordinate = 0 then
        (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) * MvPolynomial.X 1
        else MvPolynomial.X 0 ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n)
          (MvPolynomial.monomial exponent (1 : ℂ))) =
      exponent 0 • (Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1) +
        exponent 1 • (n • Finsupp.single 0 1) := by
  let order := MonomialOrder.lex (σ := Fin 2)
  have hfirst : (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) ≠ 0 := by simp
  have hsecond : (MvPolynomial.X (1 : Fin 2) : CoordinatePolynomial) ≠ 0 := by simp
  have hhigher := auxiliary_higherInvariant_ne_zero n hpositive
  have hone : (1 : Fin 2) ≠ 0 := by decide
  simp only [MvPolynomial.monomial_fin_two, map_mul, map_pow,
    MvPolynomial.aeval_X, map_one, one_mul, hone, ↓reduceIte]
  simp only [← map_pow (MvPolynomial.C : ℂ →+* CoordinatePolynomial)]
  rw [order.degree_mul (pow_ne_zero _ (mul_ne_zero hfirst hsecond))
    (pow_ne_zero _ hhigher), order.degree_pow, order.degree_pow,
    order.degree_mul hfirst hsecond, order.degree_X, order.degree_X,
    auxiliary_higherInvariant_leadingDegree n hpositive]

/-- The ordinary-coordinate expressions for the basic invariants are algebraically independent. -/
theorem _root_.Schubert.Dihedral.Invariants.generators_independent (n : ℕ) (hpositive : 0 < n) :
    AlgebraicIndependent ℂ (fun coordinate : Fin 2 => if coordinate = 0 then
      (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) * MvPolynomial.X 1
      else MvPolynomial.X 0 ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n) := by
  let evaluation : CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial :=
    MvPolynomial.aeval (fun coordinate : Fin 2 => if coordinate = 0 then
    (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) * MvPolynomial.X 1
    else MvPolynomial.X 0 ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n)
  have hnonzero : ∀ exponent : Fin 2 →₀ ℕ,
      evaluation (MvPolynomial.monomial exponent (1 : ℂ)) ≠ 0 := by
    intro exponent
    have hone : (1 : Fin 2) ≠ 0 := by decide
    simp only [evaluation, MvPolynomial.monomial_fin_two, map_mul, map_pow, MvPolynomial.aeval_X,
      map_one, one_mul, hone, ↓reduceIte]
    simp only [← map_pow (MvPolynomial.C : ℂ →+* CoordinatePolynomial)]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (by simp) (by simp)))
      (pow_ne_zero _ (auxiliary_higherInvariant_ne_zero n hpositive))
  have hdegree : Function.Injective (fun exponent : Fin 2 →₀ ℕ =>
      (MonomialOrder.lex (σ := Fin 2)).degree
        (evaluation (MvPolynomial.monomial exponent (1 : ℂ)))) :=
    by
      intro first second hequal
      apply basicInvariant_leadingDegree_injective n hpositive
      exact (_root_.Schubert.Dihedral.Invariants.monomial_leading_degree n hpositive
        first).symm.trans
        (hequal.trans (_root_.Schubert.Dihedral.Invariants.monomial_leading_degree n hpositive
          second))
  have hindependent := _root_.Schubert.Dihedral.LeadingDegree.independent_of_injective
    (MonomialOrder.lex (σ := Fin 2))
    (fun exponent : Fin 2 →₀ ℕ => evaluation (MvPolynomial.monomial exponent (1 : ℂ)))
    hnonzero hdegree
  apply algebraicIndependent_iff.mpr
  intro polynomial hpolynomial
  have hequal : Finsupp.linearCombination ℂ
      (fun exponent : Fin 2 →₀ ℕ => evaluation (MvPolynomial.monomial exponent (1 : ℂ)))
      polynomial.coeff = 0 := by
    rw [Finsupp.linearCombination_apply]
    change ∑ exponent ∈ polynomial.support,
      polynomial.coeff exponent • evaluation (MvPolynomial.monomial exponent (1 : ℂ)) = 0
    rw [← hpolynomial]
    conv_rhs => rw [polynomial.as_sum, map_sum]
    apply Finset.sum_congr rfl
    intro exponent _
    simp only [MvPolynomial.monomial_eq, map_mul, map_one, one_mul,
      MvPolynomial.smul_eq_C_mul]
    have hconstant : evaluation (MvPolynomial.C (polynomial.coeff exponent)) =
        MvPolynomial.C (polynomial.coeff exponent) := evaluation.commutes _
    rw [hconstant]
  have hcoefficients := (linearIndependent_iff.mp hindependent) _ hequal
  exact AddMonoidAlgebra.ext hcoefficients

/-- The basic invariant generators are algebraically independent. -/
theorem basicInvariants_algebraicIndependent (n : ℕ) (hpositive : 0 < n) :
    AlgebraicIndependent ℂ (fun coordinate : Fin 2 =>
      if coordinate = 0 then quadraticInvariant else higherInvariant n) := by
  have hequal : MvPolynomial.aeval (fun coordinate : Fin 2 =>
      if coordinate = 0 then quadraticInvariant else higherInvariant n) =
      auxiliaryCoordinateEquiv.toAlgHom.comp (MvPolynomial.aeval (fun coordinate : Fin 2 =>
        if coordinate = 0 then
          (MvPolynomial.X (0 : Fin 2) : CoordinatePolynomial) * MvPolynomial.X 1
        else MvPolynomial.X 0 ^ n + MvPolynomial.C ((-1 : ℂ) ^ n) * MvPolynomial.X 1 ^ n)) := by
    ext coordinate : 1
    fin_cases coordinate <;>
      simp [AlgHom.comp_apply, auxiliaryCoordinateEquiv, auxiliaryCoordinateHom,
        quadraticInvariant, higherInvariant]
  rw [algebraicIndependent_iff_injective_aeval, hequal]
  exact auxiliaryCoordinateEquiv.injective.comp
    (algebraicIndependent_iff_injective_aeval.mp
      (_root_.Schubert.Dihedral.Invariants.generators_independent n hpositive))

end Schubert.Dihedral
