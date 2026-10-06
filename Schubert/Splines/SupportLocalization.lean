import Schubert.Splines.HomogeneousDivisibility

/-! # Minimal-degree localization and propagation across transverse edges -/

namespace Schubert.Splines

variable {K P : Type*} [Field K]

/-- A homogeneous multiple of the same degree is a constant multiple, including zero. -/
theorem homogeneous_eq_C_mul_of_dvd {divisor value : MvPolynomial P K} {degree : ℕ}
    (hdivisor : divisor.IsHomogeneous degree) (hvalue : value.IsHomogeneous degree)
    (hdivides : divisor ∣ value) : ∃ scalar : K, value = MvPolynomial.C scalar * divisor := by
  by_cases hzero : value = 0
  · exact ⟨0, by simp [hzero]⟩
  obtain ⟨factor, rfl⟩ := hdivides
  have hdivisorNonzero : divisor ≠ 0 := left_ne_zero_of_mul hzero
  have hfactorNonzero : factor ≠ 0 := right_ne_zero_of_mul hzero
  have hdegree := hvalue.totalDegree hzero
  rw [MvPolynomial.totalDegree_mul_of_isDomain hdivisorNonzero hfactorNonzero,
    hdivisor.totalDegree hdivisorNonzero] at hdegree
  have hfactorDegree : factor.totalDegree = 0 := by omega
  refine ⟨factor.coeff 0, ?_⟩
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hfactorDegree, mul_comm]
  simp

/-- A transverse positive-degree label cannot divide a nonzero constant multiple. -/
theorem not_dvd_C_mul_of_relPrime {label product : MvPolynomial P K} {scalar : K}
    (hdegree : 0 < label.totalDegree) (hrelPrime : IsRelPrime label product)
    (hscalar : scalar ≠ 0) : ¬label ∣ MvPolynomial.C scalar * product := by
  intro hdivides
  have hconstant := hrelPrime.dvd_of_dvd_mul_right hdivides
  have hbound := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hconstant
    (MvPolynomial.C_ne_zero.mpr hscalar)
  simp only [MvPolynomial.totalDegree_C] at hbound
  omega

namespace IdealLabeledGraph

variable {V E : Type*} (graph : IdealLabeledGraph (MvPolynomial P K) V E)

/-- A nonzero localized value propagates across any transverse internal edge. -/
theorem target_ne_zero_of_localized_source (value : graph.Spline) (edge : E)
    (label product : MvPolynomial P K) (scalar : K)
    (hlabel : graph.label edge = Ideal.span {label})
    (hdegree : 0 < label.totalDegree) (hrelPrime : IsRelPrime label product)
    (hscalar : scalar ≠ 0)
    (hsource : (value : V → MvPolynomial P K) (graph.source edge) =
      MvPolynomial.C scalar * product) :
    (value : V → MvPolynomial P K) (graph.target edge) ≠ 0 := by
  intro hzero
  have hdivides := graph.label_dvd_of_target_eq_zero value edge label hlabel hzero
  rw [hsource] at hdivides
  exact not_dvd_C_mul_of_relPrime hdegree hrelPrime hscalar hdivides

/-- Nonzero localized values agree in presence across a transverse internal edge. -/
theorem _root_.Schubert.Splines.IdealLabeledGraph.localized_nonzero_iff
    (value : graph.Spline) (edge : E) (label firstProduct secondProduct : MvPolynomial P K)
    (firstScalar secondScalar : K) (hlabel : graph.label edge = Ideal.span {label})
    (hdegree : 0 < label.totalDegree)
    (hfirstPrime : IsRelPrime label firstProduct)
    (hsecondPrime : IsRelPrime label secondProduct)
    (hfirst : (value : V → MvPolynomial P K) (graph.source edge) =
      MvPolynomial.C firstScalar * firstProduct)
    (hsecond : (value : V → MvPolynomial P K) (graph.target edge) =
      MvPolynomial.C secondScalar * secondProduct) :
    (value : V → MvPolynomial P K) (graph.source edge) ≠ 0 ↔
      (value : V → MvPolynomial P K) (graph.target edge) ≠ 0 := by
  constructor
  · intro hnonzero
    have hscalar : firstScalar ≠ 0 := by
      intro hzero
      apply hnonzero
      simp [hfirst, hzero]
    exact graph.target_ne_zero_of_localized_source value edge label firstProduct firstScalar
      hlabel hdegree hfirstPrime hscalar hfirst
  · intro hnonzero hzero
    have hscalar : secondScalar ≠ 0 := by
      intro hscalarZero
      apply hnonzero
      simp [hsecond, hscalarZero]
    have hcondition := graph.spline_condition value edge
    rw [hlabel, hzero, zero_sub] at hcondition
    have hdivides : label ∣ (value : V → MvPolynomial P K) (graph.target edge) := by
      simpa only [dvd_neg] using Ideal.mem_span_singleton.mp hcondition
    rw [hsecond] at hdivides
    exact not_dvd_C_mul_of_relPrime hdegree hsecondPrime hscalar hdivides

/-- Connectivity makes nonzero presence constant for a localized spline on a subset. -/
theorem nonzero_presence_iff_of_localized (selected : Set V) (base : V)
    (products : V → MvPolynomial P K) (labels : E → MvPolynomial P K)
    (value : graph.Spline)
    (hlocal : ∀ vertex ∈ selected, ∃ scalar : K,
      (value : V → MvPolynomial P K) vertex = MvPolynomial.C scalar * products vertex)
    (hlabels : ∀ edge, graph.label edge = Ideal.span {labels edge})
    (htransverse : ∀ edge, graph.source edge ∈ selected → graph.target edge ∈ selected →
      0 < (labels edge).totalDegree ∧
        IsRelPrime (labels edge) (products (graph.source edge)) ∧
          IsRelPrime (labels edge) (products (graph.target edge)))
    (hconnected : ∀ predicate : V → Prop,
      (∀ edge, graph.source edge ∈ selected → graph.target edge ∈ selected →
        (predicate (graph.source edge) ↔ predicate (graph.target edge))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    : ∀ vertex ∈ selected, (value : V → MvPolynomial P K) vertex ≠ 0 ↔
        (value : V → MvPolynomial P K) base ≠ 0 := by
  have hinvariant : ∀ edge, graph.source edge ∈ selected → graph.target edge ∈ selected →
      ((value : V → MvPolynomial P K) (graph.source edge) ≠ 0 ↔
        (value : V → MvPolynomial P K) (graph.target edge) ≠ 0) := by
    intro edge hsource htarget
    obtain ⟨firstScalar, hfirst⟩ := hlocal _ hsource
    obtain ⟨secondScalar, hsecond⟩ := hlocal _ htarget
    obtain ⟨hdegree, hfirstPrime, hsecondPrime⟩ := htransverse edge hsource htarget
    exact graph.localized_nonzero_iff value edge
      (labels edge) _ _ firstScalar secondScalar (hlabels edge) hdegree
      hfirstPrime hsecondPrime hfirst hsecond
  intro vertex hvertex
  exact (hconnected (fun current => (value : V → MvPolynomial P K) current ≠ 0)
    hinvariant vertex hvertex)

/-- A supported minimal-degree spline is uniquely determined by its value at one vertex. -/
theorem eq_of_base_eq_of_minimal_supported (selected : Set V) (base : V)
    (products : V → MvPolynomial P K) (labels : E → MvPolynomial P K) (degree : ℕ)
    (hproducts : ∀ vertex ∈ selected, (products vertex).IsHomogeneous degree)
    (hdivides : ∀ value : graph.Spline,
      (∀ vertex ∈ selected, ((value : V → MvPolynomial P K) vertex).IsHomogeneous degree) →
      (∀ vertex ∉ selected, (value : V → MvPolynomial P K) vertex = 0) →
        ∀ vertex ∈ selected, products vertex ∣ (value : V → MvPolynomial P K) vertex)
    (hlabels : ∀ edge, graph.label edge = Ideal.span {labels edge})
    (htransverse : ∀ edge, graph.source edge ∈ selected → graph.target edge ∈ selected →
      0 < (labels edge).totalDegree ∧
        IsRelPrime (labels edge) (products (graph.source edge)) ∧
          IsRelPrime (labels edge) (products (graph.target edge)))
    (hconnected : ∀ predicate : V → Prop,
      (∀ edge, graph.source edge ∈ selected → graph.target edge ∈ selected →
        (predicate (graph.source edge) ↔ predicate (graph.target edge))) →
          ∀ vertex ∈ selected, predicate vertex ↔ predicate base)
    (first second : graph.Spline)
    (hfirstDegree : ∀ vertex ∈ selected,
      ((first : V → MvPolynomial P K) vertex).IsHomogeneous degree)
    (hsecondDegree : ∀ vertex ∈ selected,
      ((second : V → MvPolynomial P K) vertex).IsHomogeneous degree)
    (hfirstSupport : ∀ vertex ∉ selected, (first : V → MvPolynomial P K) vertex = 0)
    (hsecondSupport : ∀ vertex ∉ selected, (second : V → MvPolynomial P K) vertex = 0)
    (hbase : (first : V → MvPolynomial P K) base = (second : V → MvPolynomial P K) base) :
    first = second := by
  let residual := first - second
  have hdegree : ∀ vertex ∈ selected,
      ((residual : V → MvPolynomial P K) vertex).IsHomogeneous degree := by
    intro vertex hvertex
    exact (hfirstDegree vertex hvertex).sub (hsecondDegree vertex hvertex)
  have hsupport : ∀ vertex ∉ selected,
      (residual : V → MvPolynomial P K) vertex = 0 := by
    intro vertex hvertex
    change (first : V → MvPolynomial P K) vertex - (second : V → MvPolynomial P K) vertex = 0
    rw [hfirstSupport vertex hvertex, hsecondSupport vertex hvertex, sub_self]
  have hlocal : ∀ vertex ∈ selected, ∃ scalar : K,
      (residual : V → MvPolynomial P K) vertex = MvPolynomial.C scalar * products vertex := by
    intro vertex hvertex
    exact homogeneous_eq_C_mul_of_dvd (hproducts vertex hvertex) (hdegree vertex hvertex)
      (hdivides residual hdegree hsupport vertex hvertex)
  have hbaseZero : (residual : V → MvPolynomial P K) base = 0 := sub_eq_zero.mpr hbase
  apply graph.spline_ext
  intro vertex
  apply sub_eq_zero.mp
  change (residual : V → MvPolynomial P K) vertex = 0
  by_cases hvertex : vertex ∈ selected
  · by_contra hnonzero
    have hbaseNonzero := (graph.nonzero_presence_iff_of_localized selected base products labels
      residual hlocal hlabels htransverse hconnected vertex hvertex).mp hnonzero
    exact hbaseNonzero hbaseZero
  · exact hsupport vertex hvertex

end IdealLabeledGraph

end Schubert.Splines
