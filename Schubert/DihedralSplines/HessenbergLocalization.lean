import Schubert.Splines.SupportLocalization
import Schubert.DihedralSplines.Grading
import Schubert.Dihedral.RootPolynomialAction

/-! # Boundary localization for arbitrary subsets of a Hessenberg graph -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines
open scoped Classical

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergSpace n hthree)

/-- Labels of edges leaving a support subset jointly divide its spline value. -/
theorem hessenberg_boundary_product_dvd (selected : Set (DihedralGroup n))
    (value : HessenbergSpline ideal)
    (hsupport : ∀ vertex ∉ selected,
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (vertex : DihedralGroup n) :
    (∏ index ∈ ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected),
      polynomialAction n vertex (rootPolynomial n index)) ∣
        (value : DihedralGroup n → CoordinatePolynomial) vertex := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro first _ second _ hne
    exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime n vertex first second hne
  · intro index hindex
    obtain ⟨hroot, houtside⟩ := Finset.mem_filter.mp hindex
    have hcondition := hessenbergSpline_condition ideal value vertex index hroot
    change polynomialAction n vertex (rootPolynomial n index) ∣
      (value : DihedralGroup n → CoordinatePolynomial) vertex -
        (value : DihedralGroup n → CoordinatePolynomial) (vertex * rootReflection index)
      at hcondition
    simpa only [hsupport _ houtside, sub_zero] using hcondition

/-- The outgoing label product has degree equal to its number of boundary roots. -/
theorem hessenberg_boundary_product_homogeneous (selected : Set (DihedralGroup n))
    (vertex : DihedralGroup n) :
    (∏ index ∈ ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected),
      polynomialAction n vertex (rootPolynomial n index)).IsHomogeneous
        (ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected)).card := by
  classical
  have hproduct := MvPolynomial.IsHomogeneous.prod
    (ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected))
    (fun index => polynomialAction n vertex (rootPolynomial n index)) (fun _ => 1)
    (fun index _ => polynomialAction_isHomogeneous n vertex
      (rootPolynomial_isHomogeneous n index))
  simpa using hproduct

/-- At the boundary degree, a supported homogeneous value is a scalar times the boundary product. -/
theorem hessenberg_boundary_localization (selected : Set (DihedralGroup n))
    (value : HessenbergSpline ideal) (degree : ℕ)
    (hsupport : ∀ vertex ∉ selected,
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hdegree : value ∈ (hessenbergGraph ideal).homogeneousPiece degree)
    (vertex : DihedralGroup n)
    (hcard : (ideal.roots.filter
      (fun index => vertex * rootReflection index ∉ selected)).card = degree) :
    ∃ scalar : ℂ, (value : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.C scalar *
        ∏ index ∈ ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected),
          polynomialAction n vertex (rootPolynomial n index) := by
  classical
  apply homogeneous_eq_C_mul_of_dvd (degree := degree)
  · rw [← hcard]
    exact hessenberg_boundary_product_homogeneous ideal selected vertex
  · exact hdegree vertex
  · exact hessenberg_boundary_product_dvd ideal selected value hsupport vertex

/-- An internal edge label is transverse to every outgoing boundary label at its source. -/
theorem _root_.Schubert.DihedralSplines.IndexedLocalization.internal_boundary_relPrime (selected :
  Set (DihedralGroup n))
    (vertex : DihedralGroup n) (index : PositiveRootIndex n)
    (htarget : vertex * rootReflection index ∈ selected) :
    IsRelPrime (polynomialAction n vertex (rootPolynomial n index))
      (∏ other ∈ ideal.roots.filter (fun other => vertex * rootReflection other ∉ selected),
        polynomialAction n vertex (rootPolynomial n other)) := by
  classical
  apply IsRelPrime.prod_right
  intro other hother
  apply _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime n vertex index other
  intro heq
  subst other
  exact (Finset.mem_filter.mp hother).2 htarget

/-- Internal edge labels are transverse to both endpoint boundary products and have degree one. -/
theorem hessenberg_internal_edge_transverse (selected : Set (DihedralGroup n))
    (vertex : DihedralGroup n) (index : PositiveRootIndex n)
    (hsource : vertex ∈ selected) (htarget : vertex * rootReflection index ∈ selected) :
    0 < (polynomialAction n vertex (rootPolynomial n index)).totalDegree ∧
      IsRelPrime (polynomialAction n vertex (rootPolynomial n index))
        (∏ other ∈ ideal.roots.filter (fun other => vertex * rootReflection other ∉ selected),
          polynomialAction n vertex (rootPolynomial n other)) ∧
      IsRelPrime (polynomialAction n vertex (rootPolynomial n index))
        (∏ other ∈ ideal.roots.filter
          (fun other => (vertex * rootReflection index) * rootReflection other ∉ selected),
          polynomialAction n (vertex * rootReflection index) (rootPolynomial n other)) := by
  classical
  refine ⟨?_, _root_.Schubert.DihedralSplines.IndexedLocalization.internal_boundary_relPrime ideal
    selected vertex index htarget, ?_⟩
  · rw [(polynomialAction_isHomogeneous n vertex (rootPolynomial_isHomogeneous n index)).totalDegree
      (polynomialAction_rootPolynomial_ne_zero n vertex index)]
    decide
  · have hreturn : (vertex * rootReflection index) * rootReflection index ∈ selected := by
      rw [mul_assoc, rootReflection_mul_self, mul_one]
      exact hsource
    have hprime := _root_.Schubert.DihedralSplines.IndexedLocalization.internal_boundary_relPrime
      ideal selected
      (vertex * rootReflection index) index hreturn
    have hreverse : polynomialAction n (vertex * rootReflection index) (rootPolynomial n index) =
        -polynomialAction n vertex (rootPolynomial n index) :=
      (dihedralReflectionData n hthree).reflection_label_reverse vertex index
    rw [hreverse] at hprime
    simpa only [IsRelPrime, dvd_neg] using hprime

/-- At uniform boundary degree, connected support makes nonzero presence constant. -/
theorem hessenberg_localized_nonzero_presence (selected : Set (DihedralGroup n))
    (base : DihedralGroup n) (degree : ℕ)
    (hcard : ∀ vertex ∈ selected, (ideal.roots.filter
      (fun index => vertex * rootReflection index ∉ selected)).card = degree)
    (hconnected : ∀ predicate : DihedralGroup n → Prop,
      (∀ vertex ∈ selected, ∀ index ∈ ideal.roots, vertex * rootReflection index ∈ selected →
        (predicate vertex ↔ predicate (vertex * rootReflection index))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    (value : HessenbergSpline ideal)
    (hsupport : ∀ vertex ∉ selected,
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hdegree : value ∈ (hessenbergGraph ideal).homogeneousPiece degree) :
    ∀ vertex ∈ selected, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 ↔
      (value : DihedralGroup n → CoordinatePolynomial) base ≠ 0 := by
  classical
  let products := fun vertex =>
    ∏ index ∈ ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected),
      polynomialAction n vertex (rootPolynomial n index)
  let labels := fun edge : DihedralGroup n × {index // index ∈ ideal.roots} =>
    polynomialAction n edge.1 (rootPolynomial n edge.2)
  apply (hessenbergGraph ideal).nonzero_presence_iff_of_localized
    selected base products labels value
  · intro vertex hvertex
    exact hessenberg_boundary_localization ideal selected value degree hsupport hdegree
      vertex (hcard vertex hvertex)
  · intro edge
    rfl
  · rintro ⟨vertex, index, _⟩ hsource htarget
    exact hessenberg_internal_edge_transverse ideal selected vertex index hsource htarget
  · intro predicate hinvariant vertex hvertex
    apply hconnected predicate ?_ vertex hvertex
    intro source hsource index hindex htarget
    exact hinvariant (source, ⟨index, hindex⟩) hsource htarget

/-- A nonzero spline at uniform boundary degree has a nonzero boundary coefficient everywhere. -/
theorem _root_.Schubert.DihedralSplines.IndexedLocalization.coefficients_ne_zero (selected : Set
  (DihedralGroup n))
    (base : DihedralGroup n) (degree : ℕ)
    (hcard : ∀ vertex ∈ selected, (ideal.roots.filter
      (fun index => vertex * rootReflection index ∉ selected)).card = degree)
    (hconnected : ∀ predicate : DihedralGroup n → Prop,
      (∀ vertex ∈ selected, ∀ index ∈ ideal.roots, vertex * rootReflection index ∈ selected →
        (predicate vertex ↔ predicate (vertex * rootReflection index))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    (value : HessenbergSpline ideal) (hnonzero : value ≠ 0)
    (hsupport : ∀ vertex ∉ selected,
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hdegree : value ∈ (hessenbergGraph ideal).homogeneousPiece degree) :
    ∀ vertex ∈ selected, ∃ scalar : ℂ, scalar ≠ 0 ∧
      (value : DihedralGroup n → CoordinatePolynomial) vertex = MvPolynomial.C scalar *
        ∏ index ∈ ideal.roots.filter (fun index => vertex * rootReflection index ∉ selected),
          polynomialAction n vertex (rootPolynomial n index) := by
  classical
  obtain ⟨nonzeroVertex, hnonzeroVertex⟩ : ∃ vertex,
      (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hnonzero
    exact (hessenbergGraph ideal).spline_ext hnone
  have hselected : nonzeroVertex ∈ selected := by
    by_contra houtside
    exact hnonzeroVertex (hsupport _ houtside)
  have hpresence := hessenberg_localized_nonzero_presence ideal selected base degree
    hcard hconnected value hsupport hdegree
  have hbase := (hpresence nonzeroVertex hselected).mp hnonzeroVertex
  intro vertex hvertex
  obtain ⟨scalar, hscalar⟩ := hessenberg_boundary_localization ideal selected value degree
    hsupport hdegree vertex (hcard vertex hvertex)
  refine ⟨scalar, ?_, hscalar⟩
  intro hzero
  have hvalueZero : (value : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
    simp [hscalar, hzero]
  exact ((hpresence vertex hvertex).mpr hbase) hvalueZero

/-- Supported splines of the uniform boundary degree are determined by one vertex value. -/
theorem hessenberg_localized_eq_of_base_eq (selected : Set (DihedralGroup n))
    (base : DihedralGroup n) (degree : ℕ)
    (hcard : ∀ vertex ∈ selected, (ideal.roots.filter
      (fun index => vertex * rootReflection index ∉ selected)).card = degree)
    (hconnected : ∀ predicate : DihedralGroup n → Prop,
      (∀ vertex ∈ selected, ∀ index ∈ ideal.roots, vertex * rootReflection index ∈ selected →
        (predicate vertex ↔ predicate (vertex * rootReflection index))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    (first second : HessenbergSpline ideal)
    (hfirstSupport : ∀ vertex ∉ selected,
      (first : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hsecondSupport : ∀ vertex ∉ selected,
      (second : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hfirstDegree : first ∈ (hessenbergGraph ideal).homogeneousPiece degree)
    (hsecondDegree : second ∈ (hessenbergGraph ideal).homogeneousPiece degree)
    (hbase : (first : DihedralGroup n → CoordinatePolynomial) base =
      (second : DihedralGroup n → CoordinatePolynomial) base) : first = second := by
  let residual := first - second
  have hsupport : ∀ vertex ∉ selected,
      (residual : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
    intro vertex hvertex
    change (first : DihedralGroup n → CoordinatePolynomial) vertex -
      (second : DihedralGroup n → CoordinatePolynomial) vertex = 0
    rw [hfirstSupport vertex hvertex, hsecondSupport vertex hvertex, sub_self]
  have hdegree : residual ∈ (hessenbergGraph ideal).homogeneousPiece degree :=
    (hessenbergGraph ideal).homogeneousPiece degree |>.sub_mem hfirstDegree hsecondDegree
  have hbaseZero : (residual : DihedralGroup n → CoordinatePolynomial) base = 0 :=
    sub_eq_zero.mpr hbase
  have hpresence := hessenberg_localized_nonzero_presence ideal selected base degree
    hcard hconnected residual hsupport hdegree
  apply (hessenbergGraph ideal).spline_ext
  intro vertex
  apply sub_eq_zero.mp
  change (residual : DihedralGroup n → CoordinatePolynomial) vertex = 0
  by_cases hvertex : vertex ∈ selected
  · by_contra hnonzero
    exact ((hpresence vertex hvertex).mp hnonzero) hbaseZero
  · exact hsupport vertex hvertex

/-- If a nonzero supported minimal-degree spline exists, its normalized version exists uniquely. -/
theorem _root_.Schubert.DihedralSplines.IndexedLocalization.existsUnique_normalized (selected : Set
  (DihedralGroup n))
    (base : DihedralGroup n) (hbase : base ∈ selected) (degree : ℕ)
    (hcard : ∀ vertex ∈ selected, (ideal.roots.filter
      (fun index => vertex * rootReflection index ∉ selected)).card = degree)
    (hconnected : ∀ predicate : DihedralGroup n → Prop,
      (∀ vertex ∈ selected, ∀ index ∈ ideal.roots, vertex * rootReflection index ∈ selected →
        (predicate vertex ↔ predicate (vertex * rootReflection index))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    (value : HessenbergSpline ideal) (hnonzero : value ≠ 0)
    (hsupport : ∀ vertex ∉ selected,
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hdegree : value ∈ (hessenbergGraph ideal).homogeneousPiece degree) :
    ∃! normalized : HessenbergSpline ideal,
      (∀ vertex ∉ selected,
        (normalized : DihedralGroup n → CoordinatePolynomial) vertex = 0) ∧
      normalized ∈ (hessenbergGraph ideal).homogeneousPiece degree ∧
      (normalized : DihedralGroup n → CoordinatePolynomial) base =
        ∏ index ∈ ideal.roots.filter (fun index => base * rootReflection index ∉ selected),
          polynomialAction n base (rootPolynomial n index) := by
  classical
  obtain ⟨scalar, hscalarNonzero, hscalar⟩ :=
    _root_.Schubert.DihedralSplines.IndexedLocalization.coefficients_ne_zero ideal
    selected base degree hcard hconnected value hnonzero hsupport hdegree base hbase
  let normalized : HessenbergSpline ideal := scalar⁻¹ • value
  have hnormalizedSupport : ∀ vertex ∉ selected,
      (normalized : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
    intro vertex hvertex
    change scalar⁻¹ • (value : DihedralGroup n → CoordinatePolynomial) vertex = 0
    rw [hsupport vertex hvertex, smul_zero]
  have hnormalizedDegree : normalized ∈ (hessenbergGraph ideal).homogeneousPiece degree :=
    (hessenbergGraph ideal).homogeneousPiece degree |>.smul_mem scalar⁻¹ hdegree
  have hnormalizedBase : (normalized : DihedralGroup n → CoordinatePolynomial) base =
      ∏ index ∈ ideal.roots.filter (fun index => base * rootReflection index ∉ selected),
        polynomialAction n base (rootPolynomial n index) := by
    change scalar⁻¹ • (value : DihedralGroup n → CoordinatePolynomial) base = _
    rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    rw [hscalar, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hscalarNonzero, map_one, one_mul]
  refine ⟨normalized, ⟨hnormalizedSupport, hnormalizedDegree, hnormalizedBase⟩, ?_⟩
  intro other hother
  exact hessenberg_localized_eq_of_base_eq ideal selected base degree hcard hconnected
    other normalized hother.1 hnormalizedSupport hother.2.1 hnormalizedDegree
    (hother.2.2.trans hnormalizedBase.symm)

end Schubert.DihedralSplines
