import Schubert.DihedralSplines.BoundaryPropagation

/-! # Isolating coefficients in relations of geometric boundary-product functions -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines
open scoped BigOperators Classical

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

/-- The displayed boundary-product function for arbitrary pointwise scalar coefficients. -/
def boundaryFunction (vertices : Set (DihedralGroup n)) (coefficient : DihedralGroup n → ℂ) :
    DihedralGroup n → CoordinatePolynomial := fun vertex =>
  if vertex ∈ vertices then
    MvPolynomial.C (coefficient vertex) * selected.boundaryProduct vertices vertex else 0

/-- An outgoing selected label divides the boundary function at its initial vertex. -/
theorem boundaryFunction_dvd (vertices : Set (DihedralGroup n))
    (coefficient : DihedralGroup n → ℂ) (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hselected : alpha.val ∈ selected) (houtside : vertex * alpha.reflection ∉ vertices) :
    polynomialAction n vertex alpha.form ∣ selected.boundaryFunction vertices coefficient vertex :=
  by
  by_cases hinside : vertex ∈ vertices
  · rw [boundaryFunction, ite_eq_left hinside]
    apply Dvd.dvd.mul_left
    have hmem := (selected.mem_boundaryRoots vertices vertex alpha).mpr ⟨hselected, houtside⟩
    have hdivides := Finset.dvd_prod_of_mem
      (fun beta : PositiveRoot n => linearPolynomial (complexify (realAction n vertex beta.val)))
      hmem
    simpa only [boundaryProduct, PositiveRoot.action_form] using hdivides
  · rw [boundaryFunction, ite_eq_right hinside]
    exact dvd_zero _

/-- A selected edge internal to one support and absent from all active others isolates its scalar.
-/
theorem coefficient_zero {I : Type*} [Fintype I] (supports : I → Set (DihedralGroup n))
    (coefficient : I → DihedralGroup n → ℂ) (weights : I → ℂ) (index : I)
    (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hselected : alpha.val ∈ selected) (hsource : vertex ∈ supports index)
    (hinternal : vertex * alpha.reflection ∈ supports index)
    (hcoefficient : coefficient index vertex ≠ 0)
    (hother : ∀ other, other ≠ index → weights other ≠ 0 → vertex ∈ supports other →
      vertex * alpha.reflection ∉ supports other)
    (hrelation : ∑ other : I, MvPolynomial.C (weights other) *
      selected.boundaryFunction (supports other) (coefficient other) vertex = 0) :
    weights index = 0 := by
  by_contra hweight
  let label := polynomialAction n vertex alpha.form
  have hothers : label ∣ ∑ other ∈ (Finset.univ : Finset I).erase index,
      MvPolynomial.C (weights other) *
        selected.boundaryFunction (supports other) (coefficient other) vertex := by
    apply Finset.dvd_sum
    intro other hotherMem
    by_cases hzero : weights other = 0
    · simp only [hzero, map_zero, zero_mul]
      exact dvd_zero _
    · by_cases hinside : vertex ∈ supports other
      · exact (selected.boundaryFunction_dvd _ _ vertex alpha hselected
          (hother other (Finset.mem_erase.mp hotherMem).1 hzero hinside)).mul_left _
      · simp only [boundaryFunction, ite_eq_right hinside, mul_zero]
        exact dvd_zero _
  have hisolate : MvPolynomial.C (weights index) *
      selected.boundaryFunction (supports index) (coefficient index) vertex =
      -(∑ other ∈ (Finset.univ : Finset I).erase index,
        MvPolynomial.C (weights other) *
          selected.boundaryFunction (supports other) (coefficient other) vertex) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ index)] at hrelation
    rw [add_comm] at hrelation
    exact eq_neg_of_add_eq_zero_left hrelation
  have hdivides : label ∣ MvPolynomial.C (weights index * coefficient index vertex) *
      selected.boundaryProduct (supports index) vertex := by
    have hdvd := hothers.neg_right
    rw [← hisolate, boundaryFunction, ite_eq_left hsource, ← mul_assoc, ← map_mul] at hdvd
    exact hdvd
  have hform : label.IsHomogeneous 1 := by
    apply polynomialAction_isHomogeneous n vertex
    rw [alpha.form_index]
    exact rootPolynomial_isHomogeneous n alpha.index
  have hnonzero : label ≠ 0 := by
    intro heq
    apply alpha.form_ne_zero
    exact (polynomialAction n vertex).injective (heq.trans (map_zero _).symm)
  have hdegree : 0 < label.totalDegree := by
    rw [hform.totalDegree hnonzero]
    exact Nat.zero_lt_one
  exact Schubert.Splines.not_dvd_C_mul_of_relPrime hdegree
    (selected.boundary_relPrime _ vertex alpha hinternal)
    (mul_ne_zero hweight hcoefficient) hdivides

/-- An evaluation supported in just one active term isolates its scalar. -/
theorem coefficient_zero_terminal {I : Type*} [Fintype I]
    (supports : I → Set (DihedralGroup n)) (coefficient : I → DihedralGroup n → ℂ)
    (weights : I → ℂ) (index : I) (vertex : DihedralGroup n)
    (hsource : vertex ∈ supports index) (hcoefficient : coefficient index vertex ≠ 0)
    (hother : ∀ other, other ≠ index → weights other ≠ 0 → vertex ∉ supports other)
    (hrelation : ∑ other : I, MvPolynomial.C (weights other) *
      selected.boundaryFunction (supports other) (coefficient other) vertex = 0) :
    weights index = 0 := by
  by_contra hweight
  have hisolate : (∑ other : I, MvPolynomial.C (weights other) *
      selected.boundaryFunction (supports other) (coefficient other) vertex) =
      MvPolynomial.C (weights index) *
        selected.boundaryFunction (supports index) (coefficient index) vertex := by
    apply Finset.sum_eq_single index
    · intro other _ hne
      by_cases hzero : weights other = 0
      · simp only [hzero, map_zero, zero_mul]
      · rw [boundaryFunction, ite_eq_right (hother other hne hzero), mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  rw [hisolate, boundaryFunction, ite_eq_left hsource] at hrelation
  exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hweight)
    (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hcoefficient)
      (selected.boundaryProduct_ne_zero _ vertex)) hrelation

/-- Geometric separation of every active family proves independence of its boundary functions. -/
theorem independent_of_separation {I : Type*} [Fintype I]
    (supports : I → Set (DihedralGroup n)) (coefficient : I → DihedralGroup n → ℂ)
    (hcoefficient : ∀ index vertex, vertex ∈ supports index → coefficient index vertex ≠ 0)
    (hseparator : ∀ active : Set I, active.Nonempty →
      ∃ index ∈ active, ∃ vertex ∈ supports index,
        (∀ other ∈ active, other ≠ index → vertex ∉ supports other) ∨
        ∃ alpha : PositiveRoot n, alpha.val ∈ selected ∧
          vertex * alpha.reflection ∈ supports index ∧
          ∀ other ∈ active, other ≠ index → vertex ∈ supports other →
            vertex * alpha.reflection ∉ supports other) :
    LinearIndependent ℂ (fun index => selected.boundaryFunction (supports index)
      (coefficient index)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro weights hrelation index
  by_contra hnonzero
  obtain ⟨chosen, hchosen, vertex, hvertex, hseparate⟩ :=
    hseparator {current | weights current ≠ 0} ⟨index, hnonzero⟩
  have hevaluation : ∑ other : I, MvPolynomial.C (weights other) *
      selected.boundaryFunction (supports other) (coefficient other) vertex = 0 := by
    have heq := congrFun hrelation vertex
    simpa only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.smul_eq_C_mul, Pi.zero_apply]
      using heq
  apply hchosen
  rcases hseparate with hterminal | ⟨alpha, hselected, hinternal, hother⟩
  · exact selected.coefficient_zero_terminal supports coefficient weights chosen vertex
      hvertex (hcoefficient chosen vertex hvertex)
      (fun other hne hactive => hterminal other hactive hne) hevaluation
  · exact selected.coefficient_zero supports coefficient weights chosen vertex alpha
      hselected hvertex hinternal (hcoefficient chosen vertex hvertex)
      (fun other hne hactive hsource => hother other hactive hne hsource) hevaluation

end Schubert.Dihedral.RootSubset
