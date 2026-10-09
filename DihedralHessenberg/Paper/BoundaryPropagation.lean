import DihedralHessenberg.Paper.PaperLocalization
import DihedralHessenberg.Paper.RootConjugateEdge

/-! # Nonzero propagation on geometric internal edges -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

omit [NeZero n] in
/-- Boundary-root cardinality is the cardinality of the outgoing neighbor set. -/
theorem boundaryRoots_card (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n) :
    (selected.boundaryRoots vertices vertex).card =
      {target : DihedralGroup n | (vertex, target) ∈ selected.edges ∧ target ∉ vertices}.ncard := by
  classical
  have hset : {target : DihedralGroup n |
      (vertex, target) ∈ selected.edges ∧ target ∉ vertices} =
      ((selected.boundaryRoots vertices vertex).image
        (fun alpha => vertex * alpha.reflection) : Set (DihedralGroup n)) := by
    ext target
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image,
      selected.mem_edges, selected.mem_boundaryRoots]
    constructor
    · rintro ⟨⟨alpha, hselected, hneighbor⟩, houtside⟩
      change target = vertex * alpha.reflection at hneighbor
      exact ⟨alpha, ⟨hselected, hneighbor ▸ houtside⟩, hneighbor.symm⟩
    · rintro ⟨alpha, ⟨hselected, houtside⟩, hneighbor⟩
      exact ⟨⟨alpha, hselected, hneighbor.symm⟩, hneighbor ▸ houtside⟩
  have hinjective : Function.Injective (fun alpha : PositiveRoot n =>
      vertex * alpha.reflection) := fun _ _ h =>
    PositiveRoot.reflection_injective n (mul_left_cancel h)
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinjective]

/-- An internal reflection label is relatively prime to the outgoing boundary product. -/
theorem boundary_relPrime (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n)
    (alpha : PositiveRoot n) (hinternal : vertex * alpha.reflection ∈ vertices) :
    IsRelPrime (polynomialAction n vertex alpha.form)
      (selected.boundaryProduct vertices vertex) := by
  classical
  unfold boundaryProduct
  apply IsRelPrime.prod_right
  intro beta hbeta
  rw [← PositiveRoot.action_form vertex beta]
  apply PositiveRoot.action_relPrime vertex alpha beta
  intro heq
  subst beta
  exact ((selected.mem_boundaryRoots vertices vertex alpha).mp hbeta).2 hinternal

/-- A supported homogeneous value at boundary degree cannot vanish across an internal edge. -/
theorem propagate (vertices : Set (DihedralGroup n)) (value : selected.Spline) (degree : ℕ)
    (hhomogeneous : value ∈ selected.piece degree)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (vertex : DihedralGroup n) (alpha : PositiveRoot n) (hselected : alpha.val ∈ selected)
    (hinternal : vertex * alpha.reflection ∈ vertices)
    (hcard : (selected.boundaryRoots vertices vertex).card = degree)
    (hnonzero : (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) :
    (value : DihedralGroup n → CoordinatePolynomial) (vertex * alpha.reflection) ≠ 0 := by
  obtain ⟨scalar, hscalar⟩ := selected.localized vertices value degree hhomogeneous
    hsupport vertex hcard
  have hscalarNonzero : scalar ≠ 0 := by
    intro hzero
    apply hnonzero
    simp [hscalar, hzero]
  have hform : (polynomialAction n vertex alpha.form).IsHomogeneous 1 := by
    apply polynomialAction_isHomogeneous n vertex
    rw [alpha.form_index]
    exact rootPolynomial_isHomogeneous n alpha.index
  have hformNonzero : polynomialAction n vertex alpha.form ≠ 0 := by
    intro hzero
    apply alpha.form_ne_zero
    apply (polynomialAction n vertex).injective
    simpa only [map_zero] using hzero
  have hdegree : 0 < (polynomialAction n vertex alpha.form).totalDegree := by
    rw [hform.totalDegree hformNonzero]
    exact Nat.zero_lt_one
  intro hzero
  have hcondition := value.property vertex alpha.val hselected
  have hroot : selected.root alpha.val hselected = alpha := Subtype.ext rfl
  rw [hroot, hzero, sub_zero, ← PositiveRoot.action_form vertex alpha, hscalar] at hcondition
  exact Schubert.Splines.not_dvd_C_mul_of_relPrime hdegree
    (selected.boundary_relPrime vertices vertex alpha hinternal) hscalarNonzero hcondition

/-- Nonzero presence is constant across internal edges of uniform boundary degree. -/
theorem nonzero_edge_iff (vertices : Set (DihedralGroup n)) (value : selected.Spline)
    (degree : ℕ) (hhomogeneous : value ∈ selected.piece degree)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hcard : ∀ vertex ∈ vertices, (selected.boundaryRoots vertices vertex).card = degree)
    (source target : DihedralGroup n) (hsource : source ∈ vertices) (htarget : target ∈ vertices)
    (hedge : (source, target) ∈ selected.edges) :
    (value : DihedralGroup n → CoordinatePolynomial) source ≠ 0 ↔
      (value : DihedralGroup n → CoordinatePolynomial) target ≠ 0 := by
  constructor
  · intro hnonzero
    obtain ⟨alpha, hselected, hneighbor⟩ := (selected.mem_edges _).mp hedge
    change target = source * alpha.reflection at hneighbor
    rw [hneighbor] at htarget ⊢
    exact selected.propagate vertices value degree hhomogeneous hsupport source alpha
      hselected htarget (hcard source hsource) hnonzero
  · intro hnonzero
    obtain ⟨alpha, hselected, hneighbor⟩ :=
      (selected.mem_edges _).mp (selected.edge_symm hedge)
    change source = target * alpha.reflection at hneighbor
    rw [hneighbor] at hsource ⊢
    exact selected.propagate vertices value degree hhomogeneous hsupport target alpha
      hselected hsource (hcard target htarget) hnonzero

/-- Internal connectedness and one nonzero value force nonzero values on the entire subset. -/
theorem nonzero_on (vertices : Set (DihedralGroup n)) (value : selected.Spline)
    (degree : ℕ) (hhomogeneous : value ∈ selected.piece degree)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hcard : ∀ vertex ∈ vertices, (selected.boundaryRoots vertices vertex).card = degree)
    (base : DihedralGroup n)
    (hconnected : ∀ invariant : DihedralGroup n → Prop,
      (∀ source target, source ∈ vertices → target ∈ vertices →
        (source, target) ∈ selected.edges → invariant source = invariant target) →
      ∀ vertex ∈ vertices, invariant vertex = invariant base)
    (hbase : (value : DihedralGroup n → CoordinatePolynomial) base ≠ 0) :
    ∀ vertex ∈ vertices, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
  have heq := hconnected (fun vertex =>
    (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) (by
      intro source target hsource htarget hedge
      exact propext (selected.nonzero_edge_iff vertices value degree hhomogeneous
        hsupport hcard source target hsource htarget hedge))
  intro vertex hvertex
  rw [heq vertex hvertex]
  exact hbase

/-- A supported boundary-degree spline vanishing at one connected base is identically zero. -/
theorem eq_zero_of_base (vertices : Set (DihedralGroup n)) (value : selected.Spline)
    (degree : ℕ) (hhomogeneous : value ∈ selected.piece degree)
    (hsupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hcard : ∀ vertex ∈ vertices, (selected.boundaryRoots vertices vertex).card = degree)
    (base : DihedralGroup n)
    (hconnected : ∀ invariant : DihedralGroup n → Prop,
      (∀ source target, source ∈ vertices → target ∈ vertices →
        (source, target) ∈ selected.edges → invariant source = invariant target) →
      ∀ vertex ∈ vertices, invariant vertex = invariant base)
    (hbase : (value : DihedralGroup n → CoordinatePolynomial) base = 0) : value = 0 := by
  have heq := hconnected (fun vertex =>
    (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0) (by
      intro source target hsource htarget hedge
      exact propext (selected.nonzero_edge_iff vertices value degree hhomogeneous
        hsupport hcard source target hsource htarget hedge))
  apply Subtype.ext
  funext vertex
  change (value : DihedralGroup n → CoordinatePolynomial) vertex = 0
  by_cases hvertex : vertex ∈ vertices
  · by_contra hnonzero
    exact (Eq.mp (heq vertex hvertex) hnonzero) hbase
  · exact hsupport vertex hvertex

/-- A nonzero supported boundary-degree spline spans all such splines on a connected subset. -/
theorem scalar_unique (vertices : Set (DihedralGroup n)) (reference value : selected.Spline)
    (degree : ℕ) (hreference : reference ∈ selected.piece degree)
    (hvalue : value ∈ selected.piece degree)
    (hreferenceSupport : ∀ vertex, vertex ∉ vertices →
      (reference : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hvalueSupport : ∀ vertex, vertex ∉ vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hcard : ∀ vertex ∈ vertices, (selected.boundaryRoots vertices vertex).card = degree)
    (base : DihedralGroup n) (hbaseMem : base ∈ vertices)
    (hconnected : ∀ invariant : DihedralGroup n → Prop,
      (∀ source target, source ∈ vertices → target ∈ vertices →
        (source, target) ∈ selected.edges → invariant source = invariant target) →
      ∀ vertex ∈ vertices, invariant vertex = invariant base)
    (hbase : (reference : DihedralGroup n → CoordinatePolynomial) base ≠ 0) :
    ∃ scalar : ℂ, value = scalar • reference := by
  obtain ⟨first, hfirst⟩ := selected.localized vertices reference degree hreference
    hreferenceSupport base (hcard base hbaseMem)
  obtain ⟨second, hsecond⟩ := selected.localized vertices value degree hvalue
    hvalueSupport base (hcard base hbaseMem)
  have hfirstNonzero : first ≠ 0 := by
    intro hzero
    apply hbase
    simp [hfirst, hzero]
  let scalar := second / first
  refine ⟨scalar, sub_eq_zero.mp ?_⟩
  apply selected.eq_zero_of_base vertices (value - scalar • reference) degree
    ((selected.piece degree).sub_mem hvalue
      ((selected.piece degree).smul_mem scalar hreference))
    (fun vertex hnot => by
      change (value : DihedralGroup n → CoordinatePolynomial) vertex -
        scalar • (reference : DihedralGroup n → CoordinatePolynomial) vertex = 0
      rw [hvalueSupport vertex hnot, hreferenceSupport vertex hnot, smul_zero, sub_self])
    hcard base hconnected
  change (value : DihedralGroup n → CoordinatePolynomial) base -
    scalar • (reference : DihedralGroup n → CoordinatePolynomial) base = 0
  rw [hsecond, hfirst, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
  dsimp only [scalar]
  rw [div_mul_cancel₀ second hfirstNonzero, sub_self]

end Schubert.Dihedral.RootSubset
