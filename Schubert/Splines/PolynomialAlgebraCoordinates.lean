import Schubert.Splines.PolynomialAlgebraQuotientBasis
import Schubert.Splines.HomogeneousBasisLift

/-! # Coordinates of polynomial representatives in coefficient quotients -/

noncomputable section

namespace Schubert.Splines

/-- Descended algebra quotient coordinates are the constant coefficients of coordinates. -/
theorem polynomialAlgebraQuotientBasis_repr {K P A I : Type*} [CommRing K] [CommRing A]
    [Algebra K A] [Algebra (MvPolynomial P K) A] [IsScalarTower K (MvPolynomial P K) A]
    (basis : Module.Basis I (MvPolynomial P K) A) (value : A) (index : I) :
    (polynomialAlgebraQuotientBasis basis).repr
      (Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial P K) A)
        (MvPolynomial.idealOfVars P K)) value) index =
      (basis.repr value index).constantCoeff := by
  rw [polynomialAlgebraQuotientBasis, Module.Basis.map_repr]
  change polynomialBasisQuotientCoordinates basis
    ((polynomialVariableQuotientEquiv (K := K) (P := P) (A := A)).symm
      (Ideal.Quotient.mk _ value)) index = _
  rw [polynomialVariableQuotientEquiv]
  rfl

/-- Homogeneous lifts of algebra quotient basis classes form a polynomial basis. -/
theorem homogeneous_algebra_basis_lift {K P A I : Type*} [CommRing K] [CommRing A]
    [Fintype I] [DecidableEq I] [Algebra K A] [Algebra (MvPolynomial P K) A]
    [IsScalarTower K (MvPolynomial P K) A]
    (pieces : ℕ → Submodule K A) [DirectSum.Decomposition pieces]
    (basis : Module.Basis I (MvPolynomial P K) A) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : A),
      polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
        polynomial • value ∈ pieces (scalarDegree + valueDegree))
    (values : I → A) (hhomogeneous : ∀ index, values index ∈ pieces (weights index))
    (hquotient : ∀ index,
      Ideal.Quotient.mk (Ideal.map (algebraMap (MvPolynomial P K) A)
        (MvPolynomial.idealOfVars P K)) (values index) = Ideal.Quotient.mk _ (basis index)) :
    ∃ lifted : Module.Basis I (MvPolynomial P K) A, ∀ index, lifted index = values index := by
  classical
  let transform := basis.constr (MvPolynomial P K) values
  have htransform : ∀ index, transform (basis index) = values index :=
    basis.constr_basis _ values
  have haug : ∀ first second,
      (basis.repr (transform (basis second)) first).constantCoeff =
        if first = second then 1 else 0 := by
    intro first second
    have hentry := congrArg
      (fun value => (polynomialAlgebraQuotientBasis basis).repr value first) (hquotient second)
    rw [polynomialAlgebraQuotientBasis_repr, polynomialAlgebraQuotientBasis_repr] at hentry
    rw [htransform, hentry]
    by_cases heq : first = second <;> simp [Module.Basis.repr_self, heq]
  obtain ⟨lifted, hlifted⟩ := homogeneous_basis_lift pieces basis weights hbasis hsmul transform
    (fun index => htransform index ▸ hhomogeneous index) haug
    (Finset.univ.sup weights) (fun index => Finset.le_sup (Finset.mem_univ index))
  exact ⟨lifted, fun index => (hlifted index).trans (htransform index)⟩

end Schubert.Splines
