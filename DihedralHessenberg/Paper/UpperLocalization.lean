import DihedralHessenberg.Paper.BoundaryPropagation
import DihedralHessenberg.Paper.HessenbergUpper
import DihedralHessenberg.Paper.FlowupEquations

/-! # Nonzero boundary localization on geometric upper ideals -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Upper

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

/-- At the boundary degree, one nonzero diagonal forces nonzero boundary factors everywhere. -/
theorem localized (upper : Upper ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length upper.minimum))
    (hsupport : ∀ vertex, ¬BruhatLE n hthree upper.minimum vertex →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hbase : (value : DihedralGroup n → CoordinatePolynomial) upper.minimum ≠ 0)
    (vertex : DihedralGroup n) (hvertex : BruhatLE n hthree upper.minimum vertex) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧
      (value : DihedralGroup n → CoordinatePolynomial) vertex =
        MvPolynomial.C scalar * ideal.toRootSubset.boundaryProduct
          {current | BruhatLE n hthree upper.minimum current} vertex := by
  let vertices : Set (DihedralGroup n) :=
    {current | BruhatLE n hthree upper.minimum current}
  have hcard : ∀ current ∈ vertices,
      (ideal.toRootSubset.boundaryRoots vertices current).card =
        ideal.toRootSubset.length upper.minimum := by
    intro current hcurrent
    rw [ideal.toRootSubset.boundaryRoots_card]
    exact upper.boundary_card current hcurrent
  have hnonzero := ideal.toRootSubset.nonzero_on vertices value
    (ideal.toRootSubset.length upper.minimum) hhomogeneous hsupport hcard upper.minimum
    (fun invariant hinvariant => upper.eq_of_edges invariant hinvariant) hbase vertex hvertex
  obtain ⟨scalar, hscalar⟩ := ideal.toRootSubset.localized vertices value
    (ideal.toRootSubset.length upper.minimum) hhomogeneous hsupport vertex (hcard vertex hvertex)
  refine ⟨scalar, ?_, hscalar⟩
  intro hzero
  apply hnonzero
  simp [hscalar, hzero]

/-- A nonzero supported boundary-degree spline has precisely the full Bruhat upper support. -/
theorem support_exact (upper : Upper ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length upper.minimum))
    (hsupport : ∀ vertex, ¬BruhatLE n hthree upper.minimum vertex →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hbase : (value : DihedralGroup n → CoordinatePolynomial) upper.minimum ≠ 0)
    (vertex : DihedralGroup n) :
    (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 ↔
      BruhatLE n hthree upper.minimum vertex := by
  constructor
  · intro hnonzero
    by_contra hnot
    exact hnonzero (hsupport vertex hnot)
  · intro hvertex
    obtain ⟨scalar, hscalar, hvalue⟩ := upper.localized value hhomogeneous hsupport hbase
      vertex hvertex
    rw [hvalue]
    exact mul_ne_zero (MvPolynomial.C_ne_zero.mpr hscalar)
      (ideal.toRootSubset.boundaryProduct_ne_zero _ vertex)

end Schubert.DihedralSplines.HessenbergIdeal.Upper

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every selected upper-half recursion output has nonzero boundary localization everywhere. -/
theorem localized_high (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (current : DihedralGroup n) (hcurrent : BruhatLE n hthree vertex current) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧
      (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current =
        MvPolynomial.C scalar * ideal.toRootSubset.boundaryProduct
          {target | BruhatLE n hthree vertex target} current := by
  let upper := HessenbergIdeal.Upper.ofAscent ideal alpha hsimple vertex hascent hhalf hedge
  exact upper.localized (spline ideal vertex) (homogeneous ideal vertex)
    (support ideal vertex) (diagonal ideal vertex) current hcurrent

/-- Selected upper-half flow-up splines are nonzero precisely on their Bruhat upper ideal. -/
theorem support_high (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (current : DihedralGroup n) :
    (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current ≠ 0 ↔
      BruhatLE n hthree vertex current := by
  let upper := HessenbergIdeal.Upper.ofAscent ideal alpha hsimple vertex hascent hhalf hedge
  exact upper.support_exact (spline ideal vertex) (homogeneous ideal vertex)
    (support ideal vertex) (diagonal ideal vertex) current

end Schubert.DihedralSplines.FlowupSpline
