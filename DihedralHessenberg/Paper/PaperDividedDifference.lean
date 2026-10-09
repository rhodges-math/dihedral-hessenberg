import DihedralHessenberg.Paper.PaperGrading
import DihedralHessenberg.Paper.PaperIdeal
import DihedralHessenberg.Paper.DividedDifferenceDegree

/-! # Divided differences on geometric spline functions -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

omit [NeZero n] in
private theorem support_backend (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ∀ vertex, (ideal.splineEquiv value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ index ∈ ideal.indexed.roots, vertex * rootReflection index =
        rootReflection alpha.index * vertex := by
  intro vertex hnonzero
  obtain ⟨index, hmem, hendpoint⟩ :=
    (ideal.toRootSubset.mem_edges_iff_index _).mp (hedges vertex hnonzero)
  refine ⟨index, ?_, hendpoint.symm⟩
  change index ∈ (ideal.indexed.roots : Set (PositiveRootIndex n))
  rwa [ideal.indexed_roots]

/-- Divide the reflection dot numerator when every nonzero vertex has the selected left edge. -/
def dividedDifference (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ideal.toRootSubset.Spline :=
  ideal.splineEquiv.symm (hessenbergDividedDifference ideal.indexed
    (ideal.splineEquiv value) alpha.index (support_backend ideal value alpha hedges))

/-- The geometric divided difference satisfies the exact root-form numerator equation. -/
theorem dividedDifference_mul (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (vertex : DihedralGroup n) :
    alpha.form * (ideal.dividedDifference value alpha hedges :
        DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex -
        (ideal.toRootSubset.dot hthree alpha.reflection value :
          DihedralGroup n → CoordinatePolynomial) vertex := by
  rw [RootSubset.dot_apply]
  have hnumerator := hessenbergDividedDifference_mul_apply ideal.indexed
    (ideal.splineEquiv value) alpha.index (support_backend ideal value alpha hedges) vertex
  change rootPolynomial n alpha.index *
      (hessenbergDividedDifference ideal.indexed (ideal.splineEquiv value)
        alpha.index (support_backend ideal value alpha hedges) :
        DihedralGroup n → CoordinatePolynomial) vertex =
      (ideal.splineEquiv value : DihedralGroup n → CoordinatePolynomial) vertex -
        polynomialAction n (rootReflection alpha.index)
          ((ideal.splineEquiv value : DihedralGroup n → CoordinatePolynomial)
            ((rootReflection alpha.index)⁻¹ * vertex)) at hnumerator
  simpa [dividedDifference, splineEquiv, PositiveRoot.form_index,
    PositiveRoot.reflection] using hnumerator

/-- The root-form numerator equation uniquely determines the geometric divided difference. -/
theorem dividedDifference_unique (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (quotient : ideal.toRootSubset.Spline)
    (hquotient : ∀ vertex, alpha.form *
      (quotient : DihedralGroup n → CoordinatePolynomial) vertex =
        (value : DihedralGroup n → CoordinatePolynomial) vertex -
          (ideal.toRootSubset.dot hthree alpha.reflection value :
            DihedralGroup n → CoordinatePolynomial) vertex) :
    quotient = ideal.dividedDifference value alpha hedges := by
  apply Subtype.ext
  funext vertex
  exact mul_left_cancel₀ alpha.form_ne_zero
    ((hquotient vertex).trans (ideal.dividedDifference_mul value alpha hedges vertex).symm)

/-- A geometric divided difference lowers a positive homogeneous spline degree by one. -/
theorem dividedDifference_mem_piece (value : ideal.toRootSubset.Spline) (alpha : PositiveRoot n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (degree : ℕ) (hdegree : value ∈ ideal.toRootSubset.piece (degree + 1)) :
    ideal.dividedDifference value alpha hedges ∈ ideal.toRootSubset.piece degree := by
  intro vertex
  apply Schubert.Splines.polynomial_quotient_isHomogeneous
    (show alpha.form.IsHomogeneous 1 from by
      rw [PositiveRoot.form_index]
      exact rootPolynomial_isHomogeneous n alpha.index) alpha.form_ne_zero
  rw [ideal.dividedDifference_mul]
  have hdot := ideal.toRootSubset.dot_mem_piece hthree alpha.reflection (degree + 1)
    value hdegree vertex
  simpa only [Nat.add_comm] using (hdegree vertex).sub hdot

end Schubert.DihedralSplines.HessenbergIdeal
