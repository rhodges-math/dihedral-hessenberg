import Schubert.Splines.HomogeneousMinimalGenerators
import Schubert.Splines.PolynomialAlgebraQuotientBasis

/-! # Minimal homogeneous generators of polynomial algebras -/

noncomputable section
namespace Schubert.Splines

/-- Minimal homogeneous generators descend to a basis of the variable-ideal quotient. -/
theorem minimal_homogeneous_algebra_basis {K P A I J : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra (MvPolynomial P K) A]
    [IsScalarTower K (MvPolynomial P K) A] [Fintype I] [DecidableEq I] [Fintype J]
    (pieces : ℕ → Submodule K A) [DirectSum.Decomposition pieces]
    (basis : Module.Basis I (MvPolynomial P K) A) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : A),
      polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
        polynomial • value ∈ pieces (scalarDegree + valueDegree))
    (quotientPieces : ℕ → Submodule K (A ⧸
      Ideal.map (algebraMap (MvPolynomial P K) A) (MvPolynomial.idealOfVars P K)))
    [DirectSum.Decomposition quotientPieces]
    (hmap : ∀ degree (value : A), value ∈ pieces degree →
      Ideal.Quotient.mk _ value ∈ quotientPieces degree)
    (values : J → A) (degrees : J → ℕ)
    (hvalues : ∀ index, values index ∈ pieces (degrees index))
    (hspan : Submodule.span (MvPolynomial P K) (Set.range values) = ⊤)
    (hminimal : ∀ indices : Set J,
      Submodule.span (MvPolynomial P K) (values '' indices) = ⊤ → indices = Set.univ)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    ∃ descended : Module.Basis J K (A ⧸
      Ideal.map (algebraMap (MvPolynomial P K) A) (MvPolynomial.idealOfVars P K)),
      ∀ index, descended index = Ideal.Quotient.mk _ (values index) := by
  let transport := polynomialVariableQuotientEquiv (K := K) (P := P) (A := A)
  let order := (Submodule.orderIsoMapComap transport).symm
  let pulled : ℕ → Submodule K _ := fun degree => order (quotientPieces degree)
  have hinternal : DirectSum.IsInternal pulled := by
    have horiginal := DirectSum.Decomposition.isInternal quotientPieces
    apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · exact (iSupIndep_map_orderIso_iff order).2 horiginal.submodule_iSupIndep
    · rw [← order.map_iSup, horiginal.submodule_iSup_eq_top, order.map_top]
  let := hinternal.chooseDecomposition
  have htransport (value : A) :
      transport (Submodule.Quotient.mk value) = Ideal.Quotient.mk _ value :=
    Submodule.quotEquivOfEq_mk _ _ _ value
  have hpulled (degree : ℕ) (value : A) (hvalue : value ∈ pieces degree) :
      Submodule.Quotient.mk value ∈ pulled degree := by
    change transport (Submodule.Quotient.mk value) ∈ quotientPieces degree
    rw [htransport]
    exact hmap degree value hvalue
  obtain ⟨descended, hdescended⟩ := minimal_homogeneous_quotient_basis pieces basis weights
    hbasis hsmul pulled hpulled values degrees hvalues hspan hminimal bound hbound
  refine ⟨descended.map transport, ?_⟩
  intro index
  rw [Module.Basis.map_apply, hdescended, htransport]

end Schubert.Splines
