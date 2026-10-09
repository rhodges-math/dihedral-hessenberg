import DihedralHessenberg.Paper.SchubertLocalization
import DihedralHessenberg.Splines.SupportLocalization
import DihedralHessenberg.Paper.LeftUpperBoundary

/-! # Untransformed left-boundary products for Schubert splines -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral
open scoped Classical

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- The positive left reflections descending from an evaluation vertex outside the upper ideal. -/
def rationalRoots (vertex current : DihedralGroup n) : Finset (PositiveRoot n) := by
  classical
  exact Finset.univ.filter (fun alpha =>
    BruhatLE n hthree (alpha.reflection * current) current ∧
      alpha.reflection * current ≠ current ∧
      ¬BruhatLE n hthree vertex (alpha.reflection * current))

omit [NeZero n] in
private theorem rationalRoots_length (vertex current : DihedralGroup n) :
    rationalRoots n hthree vertex current = Finset.univ.filter (fun alpha : PositiveRoot n =>
      length n hthree (alpha.reflection * current) < length n hthree current ∧
        ¬BruhatLE n hthree vertex (alpha.reflection * current)) := by
  classical
  ext alpha
  simp only [rationalRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hbelow, _, houtside⟩
    exact ⟨(alpha.bruhat_left hthree current).mp hbelow, houtside⟩
  · rintro ⟨hshort, houtside⟩
    refine ⟨(alpha.bruhat_left hthree current).mpr hshort, ?_, houtside⟩
    intro heq
    rw [heq] at hshort
    exact (lt_irrefl _ hshort)
/-- The exact product of untransformed root forms in the rational Schubert formula. -/
def rationalProduct (vertex current : DihedralGroup n) : CoordinatePolynomial :=
  ∏ alpha ∈ rationalRoots n hthree vertex current, alpha.form

/-- The untransformed boundary product divides the Schubert value. -/
theorem rationalProduct_dvd (vertex current : DihedralGroup n) :
    rationalProduct n hthree vertex current ∣
      (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro first _ second _ hne
    have hprime := PositiveRoot.action_relPrime (1 : DihedralGroup n) first second hne
    simpa only [map_one, AlgEquiv.one_apply] using hprime
  · intro alpha hmem
    have hnot := (Finset.mem_filter.mp hmem).2.2.2
    have hdivides := (RootSubset.full_iff_left n hthree _).mp
      (spline n hthree vertex).property current alpha
    rw [support n hthree vertex _ hnot, sub_zero] at hdivides
    exact hdivides

omit [NeZero n] in
/-- Left-boundary products are homogeneous of their root count. -/
theorem rationalProduct_homogeneous (vertex current : DihedralGroup n) :
    (rationalProduct n hthree vertex current).IsHomogeneous
      (rationalRoots n hthree vertex current).card := by
  classical
  have hproduct := MvPolynomial.IsHomogeneous.prod
    (rationalRoots n hthree vertex current) (fun alpha => alpha.form) (fun _ => 1)
    (fun alpha _ => by
      rw [alpha.form_index]
      exact rootPolynomial_isHomogeneous n alpha.index)
  simpa [rationalProduct] using hproduct

/-- At the canonical root count, every upper value has a nonzero rational coefficient. -/
theorem rationalCoefficient (vertex current : DihedralGroup n)
    (habove : BruhatLE n hthree vertex current) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧
      (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current =
        MvPolynomial.C scalar * rationalProduct n hthree vertex current := by
  have hcard : (rationalRoots n hthree vertex current).card = length n hthree vertex :=
    by
    rw [rationalRoots_length]
    exact RootSubset.card_left_upper_boundary n hthree vertex current habove
  obtain ⟨scalar, hscalar⟩ := Schubert.Splines.homogeneous_eq_C_mul_of_dvd
    (by rw [← hcard]; exact rationalProduct_homogeneous n hthree vertex current)
    (homogeneous n hthree vertex current) (rationalProduct_dvd n hthree vertex current)
  refine ⟨scalar, ?_, hscalar⟩
  intro hzero
  apply nonzero_above n hthree vertex current habove
  simp [hscalar, hzero]

/-- The Schubert function has the exact rational product formula
and support coefficients. -/
theorem rational_formula (vertex : DihedralGroup n) :
    ∃ coefficient : DihedralGroup n → ℂ,
      (∀ current, coefficient current ≠ 0 ↔ BruhatLE n hthree vertex current) ∧
      ∀ current, (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current =
        MvPolynomial.C (coefficient current) * rationalProduct n hthree vertex current := by
  classical
  let coefficient : DihedralGroup n → ℂ := fun current =>
    if habove : BruhatLE n hthree vertex current then
      Classical.choose (rationalCoefficient n hthree vertex current habove)
    else 0
  refine ⟨coefficient, ?_, ?_⟩
  · intro current
    by_cases habove : BruhatLE n hthree vertex current
    · rw [show coefficient current =
        Classical.choose (rationalCoefficient n hthree vertex current habove) by
          simp only [coefficient, dite_eq_left habove]]
      exact iff_of_true
        (Classical.choose_spec (rationalCoefficient n hthree vertex current habove)).1 habove
    · simp only [coefficient, dite_eq_right habove, ne_eq, not_true_eq_false]
      exact iff_of_false not_false habove
  · intro current
    by_cases habove : BruhatLE n hthree vertex current
    · dsimp only [coefficient]
      rw [dite_eq_left habove]
      exact (Classical.choose_spec (rationalCoefficient n hthree vertex current habove)).2
    · simp only [coefficient, dite_eq_right habove, map_zero, zero_mul]
      exact support n hthree vertex current habove
end Schubert.DihedralSplines.SchubertSpline
