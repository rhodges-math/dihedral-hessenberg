import DihedralHessenberg.Paper.PaperGrading
import DihedralHessenberg.Paper.PaperIdeal
import DihedralHessenberg.Paper.TopSpline
import DihedralHessenberg.Dihedral.RankTwoRootVectors

/-! # The geometric single-vertex and top splines -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The product of transformed linear forms over the selected root vectors. -/
def labelProduct (vertex : DihedralGroup n) : CoordinatePolynomial :=
  ∏ alpha ∈ ideal.toRootSubset.finite.toFinset,
    linearPolynomial (complexify (realAction n vertex alpha))

/-- Alternating numbering preserves the specified incident-label product exactly. -/
theorem labelProduct_backend (vertex : DihedralGroup n) :
    ideal.labelProduct vertex =
      ∏ index ∈ ideal.indexed.roots, polynomialAction n vertex (rootPolynomial n index) := by
  classical
  symm
  apply Finset.prod_bij (fun index _ => positiveRoot n index)
  · intro index hindex
    exact ideal.toRootSubset.finite.mem_toFinset.mpr ((ideal.mem_indexed index).mp hindex)
  · intro first _ second _ heq
    exact positiveRoot_injective n heq
  · intro alpha halpha
    have hmem := ideal.toRootSubset.finite.mem_toFinset.mp halpha
    obtain ⟨index, rfl⟩ := ideal.positive hmem
    exact ⟨index, (ideal.mem_indexed index).mpr hmem, rfl⟩
  · intro index _
    exact PositiveRoot.action_form vertex (positiveRootEquiv n index)

/-- The incident-label product supported at one vertex is a geometric spline. -/
def singleSpline (vertex : DihedralGroup n) : ideal.toRootSubset.Spline :=
  ideal.splineEquiv.symm (⟨fun current => if current = vertex then
      ∏ index ∈ ideal.indexed.roots, polynomialAction n vertex (rootPolynomial n index) else 0,
    (dihedralReflectionData n hthree).singleProductFunction_isSpline
      ideal.indexed.roots vertex⟩ : HessenbergSpline ideal.indexed)

/-- The geometric single-vertex spline has the selected-vector product as its value. -/
theorem singleSpline_apply (vertex current : DihedralGroup n) :
    (ideal.singleSpline vertex : DihedralGroup n → CoordinatePolynomial) current =
      if current = vertex then ideal.labelProduct vertex else 0 := by
  change (if current = vertex then _ else 0) = _
  rw [ideal.labelProduct_backend]

/-- The diagonal value of a geometric single-vertex spline is nonzero. -/
theorem singleSpline_nonzero (vertex : DihedralGroup n) :
    (ideal.singleSpline vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
  rw [ideal.singleSpline_apply, ite_eq_left rfl, ideal.labelProduct_backend]
  exact Finset.prod_ne_zero_iff.mpr (fun index _ =>
    polynomialAction_rootPolynomial_ne_zero n vertex index)

/-- Every value of a single-vertex spline is homogeneous of the selected-root cardinality. -/
theorem singleSpline_mem_piece (vertex : DihedralGroup n) :
    ideal.singleSpline vertex ∈ ideal.toRootSubset.piece ideal.carrier.ncard := by
  intro current
  rw [ideal.singleSpline_apply, ideal.labelProduct_backend, ideal.ncard_indexed]
  by_cases heq : current = vertex
  · rw [ite_eq_left heq]
    have hproduct := MvPolynomial.IsHomogeneous.prod ideal.indexed.roots
      (fun index => polynomialAction n vertex (rootPolynomial n index)) (fun _ => 1)
      (fun index _ => polynomialAction_isHomogeneous n vertex
        (rootPolynomial_isHomogeneous n index))
    simpa using hproduct
  · rw [ite_eq_right heq]
    exact MvPolynomial.isHomogeneous_zero _ _ _

/-- The top spline is the single-vertex spline at the longest element. -/
def topSpline : ideal.toRootSubset.Spline := ideal.singleSpline (longestElement n hthree)

/-- The top spline has exactly the displayed product and singleton support. -/
theorem topSpline_apply (current : DihedralGroup n) :
    (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) current =
      if current = longestElement n hthree then
        ∏ alpha ∈ ideal.toRootSubset.finite.toFinset,
          linearPolynomial (complexify (realAction n (longestElement n hthree) alpha)) else 0 :=
  ideal.singleSpline_apply _ current

/-- The top spline is nonzero at the longest element. -/
theorem topSpline_nonzero :
    (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) (longestElement n hthree) ≠ 0 :=
  ideal.singleSpline_nonzero _

/-- The top spline is homogeneous of the number of selected positive root vectors. -/
theorem topSpline_mem_piece : ideal.topSpline ∈ ideal.toRootSubset.piece ideal.carrier.ncard :=
  ideal.singleSpline_mem_piece _

/-- The top spline is supported weakly above the longest element in Bruhat order. -/
theorem topSpline_support (current : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree (longestElement n hthree) current) :
    (ideal.topSpline : DihedralGroup n → CoordinatePolynomial) current = 0 := by
  rw [ideal.topSpline_apply]
  apply ite_eq_right
  intro heq
  apply hnot
  rw [heq]
  let := bruhatPartialOrder n hthree
  exact le_refl (longestElement n hthree)

end Schubert.DihedralSplines.HessenbergIdeal
