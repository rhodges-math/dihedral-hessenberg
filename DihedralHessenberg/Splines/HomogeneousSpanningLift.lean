import DihedralHessenberg.Splines.HomogeneousBasisLift

/-! # Homogeneous spanning lifts from the variable-ideal quotient -/

noncomputable section
namespace Schubert.Splines

/-- Homogeneous lifts of any quotient basis generate the polynomial module. -/
theorem homogeneous_quotient_span {K P M I J : Type*} [Field K]
    [Fintype I] [DecidableEq I] [Fintype J]
    [AddCommGroup M] [Module K M] [Module (MvPolynomial P K) M]
    [IsScalarTower K (MvPolynomial P K) M]
    (pieces : ℕ → Submodule K M) [DirectSum.Decomposition pieces]
    (basis : Module.Basis I (MvPolynomial P K) M) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hsmul : ∀ scalarDegree valueDegree (polynomial : MvPolynomial P K) (value : M),
      polynomial.IsHomogeneous scalarDegree → value ∈ pieces valueDegree →
        polynomial • value ∈ pieces (scalarDegree + valueDegree))
    (quotientPieces : ℕ → Submodule K (M ⧸
      (MvPolynomial.idealOfVars P K • (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K))
    [DirectSum.Decomposition quotientPieces]
    (quotientBasis : Module.Basis J K (M ⧸
      (MvPolynomial.idealOfVars P K • (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K))
    (values : J → M) (degrees : J → ℕ)
    (hvalues : ∀ index, values index ∈ pieces (degrees index))
    (hquotient : ∀ index, quotientBasis index = Submodule.Quotient.mk (values index))
    (hquotientBasis : ∀ index, quotientBasis index ∈ quotientPieces (degrees index))
    (hmap : ∀ index, Submodule.Quotient.mk (basis index) ∈ quotientPieces (weights index))
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    Submodule.span (MvPolynomial P K) (Set.range values) = ⊤ := by
  classical
  let variableModule := (MvPolynomial.idealOfVars P K •
    (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K
  let lifts : I → M := fun index =>
    ∑ other, quotientBasis.repr (variableModule.mkQ (basis index)) other • values other
  have hlifts : ∀ index, lifts index ∈ pieces (weights index) := by
    intro index
    apply Submodule.sum_mem
    intro other _
    by_cases heq : degrees other = weights index
    · exact Submodule.smul_mem _ _ (heq ▸ hvalues other)
    · have hzero := HomogeneousBasis.repr_zero_of_degree_ne quotientPieces quotientBasis
        degrees hquotientBasis (weights index) (hmap index) other heq
      change quotientBasis.repr (variableModule.mkQ (basis index)) other = 0 at hzero
      rw [hzero, zero_smul]
      exact Submodule.zero_mem _
  have hclasses : ∀ index, variableModule.mkQ (lifts index) =
      variableModule.mkQ (basis index) := by
    intro index
    change variableModule.mkQ (∑ other,
      quotientBasis.repr (variableModule.mkQ (basis index)) other • values other) = _
    rw [map_sum]
    simp only [map_smul]
    calc
      _ = ∑ other, quotientBasis.repr (variableModule.mkQ (basis index)) other •
          quotientBasis other := by
        apply Finset.sum_congr rfl
        intro other _
        exact congrArg (_ • ·) (hquotient other).symm
      _ = _ := quotientBasis.sum_repr _
  obtain ⟨lifted, hlifted⟩ := homogeneous_quotient_basis_lift pieces basis weights hbasis
    hsmul lifts hlifts hclasses bound hbound
  rw [Submodule.eq_top_iff_forall_basis_mem lifted]
  intro index
  rw [hlifted]
  apply Submodule.sum_mem
  intro other _
  rw [← algebraMap_smul (MvPolynomial P K)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self other))

end Schubert.Splines
