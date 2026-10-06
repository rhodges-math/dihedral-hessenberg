import Schubert.Splines.PolynomialModuleQuotientBasis
import Schubert.Splines.IdealScalarExtension

/-! # Polynomial bases of variable-ideal algebra quotients

Ideal extension agrees with scalar-ideal multiplication. Hence the module
basis descent applies directly to polynomial algebra quotients.
-/

noncomputable section

namespace Schubert.Splines

variable {K P A I : Type*} [CommRing K] [CommRing A]
variable [Algebra K A] [Algebra (MvPolynomial P K) A]
variable [IsScalarTower K (MvPolynomial P K) A]

/-- The variable-ideal module multiple and its algebra extension have the same carrier. -/
theorem variableIdeal_smul_restrictScalars :
    (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) A)).restrictScalars K =
      (Ideal.map (algebraMap (MvPolynomial P K) A)
        (MvPolynomial.idealOfVars P K)).restrictScalars K := by
  ext value
  change value ∈ MvPolynomial.idealOfVars P K •
    (⊤ : Submodule (MvPolynomial P K) A) ↔
      value ∈ Ideal.map (algebraMap (MvPolynomial P K) A) (MvPolynomial.idealOfVars P K)
  rw [← mapIdeal_restrictScalars_eq_smul_top]
  rfl

/-- Identify the variable-ideal module quotient with the algebra quotient. -/
def polynomialVariableQuotientEquiv :
    (A ⧸ (MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) A)).restrictScalars K) ≃ₗ[K]
      A ⧸ Ideal.map (algebraMap (MvPolynomial P K) A) (MvPolynomial.idealOfVars P K) :=
  Submodule.quotEquivOfEq
    ((MvPolynomial.idealOfVars P K •
      (⊤ : Submodule (MvPolynomial P K) A)).restrictScalars K)
    ((Ideal.map (algebraMap (MvPolynomial P K) A)
      (MvPolynomial.idealOfVars P K)).restrictScalars K)
    (variableIdeal_smul_restrictScalars (K := K) (P := P) (A := A))

/-- A polynomial basis descends to a coefficient basis of its variable-ideal algebra quotient. -/
def polynomialAlgebraQuotientBasis (basis : Module.Basis I (MvPolynomial P K) A) :
    Module.Basis I K (A ⧸ Ideal.map (algebraMap (MvPolynomial P K) A)
      (MvPolynomial.idealOfVars P K)) :=
  (polynomialModuleQuotientBasis basis).map polynomialVariableQuotientEquiv

/-- Each descended algebra basis vector is the quotient of its vector. -/
theorem polynomialAlgebraQuotientBasis_apply
    (basis : Module.Basis I (MvPolynomial P K) A) (index : I) :
    polynomialAlgebraQuotientBasis basis index =
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial P K) A)
        (MvPolynomial.idealOfVars P K)) (basis index) := by
  rw [polynomialAlgebraQuotientBasis,
    (polynomialModuleQuotientBasis basis).map_apply
      (polynomialVariableQuotientEquiv (K := K) (P := P) (A := A)) index,
    polynomialModuleQuotientBasis_apply]
  exact Submodule.quotEquivOfEq_mk _ _ _ (basis index)

/-- Variable-ideal algebra quotient rank equals the polynomial basis cardinality. -/
theorem polynomialAlgebraQuotientBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I (MvPolynomial P K) A) :
    Module.finrank K (A ⧸ Ideal.map (algebraMap (MvPolynomial P K) A)
      (MvPolynomial.idealOfVars P K)) = Nat.card I :=
  Module.finrank_eq_nat_card_basis (polynomialAlgebraQuotientBasis basis)

end Schubert.Splines
