import Schubert.Splines.HomogeneousSpanningLift
import Schubert.Splines.PolynomialQuotientSpan
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Minimal homogeneous polynomial generators and quotient bases -/

noncomputable section
namespace Schubert.Splines

/-- A minimal generating set contains no zero vector. -/
theorem minimal_generator_ne_zero {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] (generators : Set M) (hspan : Submodule.span R generators = ⊤)
    (hminimal : ∀ smaller ⊆ generators, Submodule.span R smaller = ⊤ →
      smaller = generators) {value : M} (hvalue : value ∈ generators) : value ≠ 0 := by
  intro hzero
  subst value
  have heq := hminimal (generators \ {0}) Set.sdiff_subset
    (Submodule.span_sdiff_singleton_zero.trans hspan)
  have hmember : (0 : M) ∈ generators \ {0} := heq.symm ▸ hvalue
  exact hmember.2 (Set.mem_singleton 0)

/-- A minimal generating set of a finite free module is finite, without an indexed premise. -/
theorem minimal_generators_finite {R M I : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [Fintype I] (basis : Module.Basis I R M) (generators : Set M)
    (hspan : Submodule.span R generators = ⊤)
    (hminimal : ∀ smaller ⊆ generators, Submodule.span R smaller = ⊤ →
      smaller = generators) : generators.Finite := by
  classical
  have hsubset : (Finset.univ.image basis : Set M) ⊆ Submodule.span R generators := by
    rw [hspan]
    exact Set.subset_univ _
  obtain ⟨finite, hfinite, hbasis⟩ := Submodule.subset_span_finite_of_subset_span hsubset
  have htop : Submodule.span R (finite : Set M) = ⊤ := by
    rw [Submodule.eq_top_iff_forall_basis_mem basis]
    intro index
    exact hbasis (Finset.mem_image.mpr ⟨index, Finset.mem_univ _, rfl⟩)
  rw [← hminimal finite hfinite htop]
  exact finite.finite_toSet

/-- Every minimal homogeneous polynomial generating family descends to a quotient basis. -/
theorem minimal_homogeneous_quotient_basis {K P M I J : Type*} [Field K]
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
    (hmap : ∀ degree (value : M), value ∈ pieces degree →
      Submodule.Quotient.mk value ∈ quotientPieces degree)
    (values : J → M) (degrees : J → ℕ)
    (hvalues : ∀ index, values index ∈ pieces (degrees index))
    (hspan : Submodule.span (MvPolynomial P K) (Set.range values) = ⊤)
    (hminimal : ∀ indices : Set J,
      Submodule.span (MvPolynomial P K) (values '' indices) = ⊤ → indices = Set.univ)
    (bound : ℕ) (hbound : ∀ index, weights index ≤ bound) :
    ∃ descended : Module.Basis J K (M ⧸
      (MvPolynomial.idealOfVars P K • (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K),
      ∀ index, descended index = Submodule.Quotient.mk (values index) := by
  classical
  let quotient := (MvPolynomial.idealOfVars P K •
    (⊤ : Submodule (MvPolynomial P K) M)).restrictScalars K
  let images : J → M ⧸ quotient := fun index => quotient.mkQ (values index)
  have hquotientSpan := polynomial_quotient_span basis values hspan
  obtain ⟨A, select, hinjective, hselectedSpan, hselected⟩ :=
    exists_linearIndependent' K images
  let : Finite A := Finite.of_injective select hinjective
  let : Fintype A := Fintype.ofFinite A
  have htop : ⊤ ≤ Submodule.span K (Set.range (images ∘ select)) := by
    rw [hselectedSpan]
    exact hquotientSpan.ge
  let selectedBasis := Module.Basis.mk hselected htop
  have hselectedValues (index : A) :
      selectedBasis index = quotient.mkQ (values (select index)) :=
    Module.Basis.mk_apply hselected htop index
  have hselectedHomogeneous (index : A) :
      selectedBasis index ∈ quotientPieces (degrees (select index)) := by
    rw [hselectedValues]
    exact hmap _ _ (hvalues _)
  have hliftedSpan := homogeneous_quotient_span pieces basis weights hbasis hsmul
    quotientPieces selectedBasis (values ∘ select) (degrees ∘ select)
    (fun index => hvalues (select index)) hselectedValues hselectedHomogeneous
    (fun index => hmap _ _ (hbasis index)) bound hbound
  have hall : Set.range select = Set.univ := hminimal (Set.range select) (by
    simpa only [Set.range_comp] using hliftedSpan)
  have hsurjective : Function.Surjective select := by
    intro index
    have hmember : index ∈ Set.range select := by rw [hall]; exact Set.mem_univ _
    exact hmember
  let equivalence := Equiv.ofBijective select ⟨hinjective, hsurjective⟩
  refine ⟨selectedBasis.reindex equivalence, ?_⟩
  intro index
  rw [Module.Basis.reindex_apply, hselectedValues]
  exact congrArg (fun other => quotient.mkQ (values other))
    (equivalence.apply_symm_apply index)

end Schubert.Splines
