import DihedralHessenberg.Paper.FlowupOrbitIndependence
import DihedralHessenberg.Paper.DominanceUpper

/-! # Independence of the two even middle-degree spline orbits -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral
open scoped Pointwise Classical
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Upper-half dot translates have the translated finite upper support. -/
theorem high_support_finset (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhigh : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (translate : DihedralGroup n) :
    Function.support (ideal.toRootSubset.dot hthree translate (spline ideal vertex) :
        DihedralGroup n → CoordinatePolynomial) =
      (translate • (Finset.univ.filter fun current => BruhatLE n hthree vertex current) :
        Finset (DihedralGroup n)) := by
  have hsupport : Function.support (spline ideal vertex :
      DihedralGroup n → CoordinatePolynomial) =
      ((Finset.univ.filter fun current => BruhatLE n hthree vertex current) :
        Set (DihedralGroup n)) := by
    ext current
    simpa only [Function.mem_support, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] using
      support_high ideal vertex alpha hsimple hascent hhigh hedge current
  rw [ideal.toRootSubset.dot_support_set hthree, hsupport]
  simp only [Finset.smul_finset_def, Finset.coe_image, smul_eq_mul]


/-- Both prescribed-simple middle orbits are jointly independent in the spline space. -/
theorem paired_middle_independent {I J : Type*} [Fintype I] [Fintype J]
    (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (firstTranslate : I → DihedralGroup n) (secondTranslate : J → DihedralGroup n)
    (hfirst : Function.Injective (fun index => ideal.toRootSubset.dot hthree
      (firstTranslate index) (spline ideal first.vertex)))
    (hsecond : Function.Injective (fun index => ideal.toRootSubset.dot hthree
      (secondTranslate index) (spline ideal second.vertex))) :
    LinearIndependent ℂ (Sum.elim
      (fun index => ideal.toRootSubset.dot hthree (firstTranslate index)
        (spline ideal first.vertex))
      (fun index => ideal.toRootSubset.dot hthree (secondTranslate index)
        (spline ideal second.vertex))) := by
  classical
  have hfirstBounds := first.even_bounds hcard hproper
  have hsecondBounds := second.even_bounds hcard hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hdepth : n - (n - half) - 1 = half - 1 := by
    have hmaximum := ideal.card_lt hproper
    rw [hcard] at hmaximum
    omega
  have hbound : 2 * (half - 1) + 1 < n := by
    simpa only [first.canonical, hdepth] using hfirstBounds.2.2
  have hselected : ∀ beta : PositiveRoot n,
      length n hthree beta.reflection ≤ 2 * (half - 1) + 1 → beta.val ∈ ideal := by
    simpa only [first.canonical, hdepth] using first.even_selected hcard hproper
  have hdisjoint := ideal.middle_even_disjoint half hcard hproper first second
  have hcross : ∀ firstIndex secondIndex,
      Function.support (ideal.toRootSubset.dot hthree (firstTranslate firstIndex)
        (spline ideal first.vertex) : DihedralGroup n → CoordinatePolynomial) ≠
      Function.support (ideal.toRootSubset.dot hthree (secondTranslate secondIndex)
        (spline ideal second.vertex) : DihedralGroup n → CoordinatePolynomial) := by
    intro firstIndex secondIndex heq
    rw [high_support_finset ideal first.vertex (simpleRoot n hthree 0) (Or.inl rfl)
        first.ascent hfirstBounds.2.1 first.selected,
      high_support_finset ideal second.vertex (simpleRoot n hthree 1) (Or.inr rfl)
        second.ascent hsecondBounds.2.1 second.selected] at heq
    have hfinset := Finset.coe_injective heq
    apply Set.disjoint_left.mp hdisjoint
      (show firstTranslate firstIndex • (Finset.univ.filter fun current =>
          BruhatLE n hthree first.vertex current) ∈
        MulAction.orbit (DihedralGroup n) (Finset.univ.filter fun current =>
          BruhatLE n hthree first.vertex current) from ⟨firstTranslate firstIndex, rfl⟩)
    rw [hfinset]
    exact ⟨secondTranslate secondIndex, rfl⟩
  have hfamily : Sum.elim
      (fun index => ideal.toRootSubset.dot hthree (firstTranslate index)
        (spline ideal first.vertex))
      (fun index => ideal.toRootSubset.dot hthree (secondTranslate index)
        (spline ideal second.vertex)) =
      (fun index : I ⊕ J => ideal.toRootSubset.dot hthree
        (Sum.elim firstTranslate secondTranslate index)
        (spline ideal (Sum.elim (fun _ => first.vertex) (fun _ => second.vertex) index))) := by
    funext index
    cases index <;> rfl
  rw [hfamily]
  apply high_family_independent ideal (half - 1) hbound hselected
    (Sum.elim (fun _ => first.vertex) (fun _ => second.vertex))
    (Sum.elim (fun _ => simpleRoot n hthree 0) (fun _ => simpleRoot n hthree 1))
    (fun index => by cases index <;> exact (by simp))
    (fun index => by cases index <;> first | exact first.ascent | exact second.ascent)
    (fun index => by cases index <;> first | exact hfirstBounds.2.1 | exact hsecondBounds.2.1)
    (fun index => by cases index <;> first | exact first.selected | exact second.selected)
    (fun index => by
      cases index with
      | inl _ =>
        change n - length n hthree first.vertex - 1 = half - 1
        rw [first.canonical]
        exact hdepth
      | inr _ =>
        change n - length n hthree second.vertex - 1 = half - 1
        rw [second.canonical]
        exact hdepth)
    (Sum.elim firstTranslate secondTranslate)
  intro firstIndex secondIndex heq
  cases firstIndex with
  | inl firstIndex =>
    cases secondIndex with
    | inl secondIndex =>
      apply congrArg Sum.inl
      apply hfirst
      exact (high_support_eq ideal first.vertex (simpleRoot n hthree 0) (Or.inl rfl)
        first.ascent hfirstBounds.2.1 first.selected _ _).mp heq
    | inr secondIndex => exact False.elim (hcross firstIndex secondIndex heq)
  | inr firstIndex =>
    cases secondIndex with
    | inl secondIndex => exact False.elim (hcross secondIndex firstIndex heq.symm)
    | inr secondIndex =>
      apply congrArg Sum.inr
      apply hsecond
      exact (high_support_eq ideal second.vertex (simpleRoot n hthree 1) (Or.inr rfl)
        second.ascent hsecondBounds.2.1 second.selected _ _).mp heq
end Schubert.DihedralSplines.FlowupSpline
