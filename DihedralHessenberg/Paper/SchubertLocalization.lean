import DihedralHessenberg.Paper.SchubertRecursion
import DihedralHessenberg.Paper.BoundaryPropagation
import DihedralHessenberg.Paper.FullUpperBoundary
import DihedralHessenberg.Paper.UpperConnectivity

/-! # Nonzero Schubert localization on full Bruhat upper ideals -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- Every Schubert spline is nonzero at every vertex of its Bruhat upper ideal. -/
theorem nonzero_above (vertex current : DihedralGroup n)
    (habove : BruhatLE n hthree vertex current) :
    (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current ≠ 0 := by
  let upper : Set (DihedralGroup n) := {target | BruhatLE n hthree vertex target}
  have hcard : ∀ target ∈ upper,
      ((RootSubset.full n).boundaryRoots upper target).card = length n hthree vertex := by
    intro target htarget
    rw [RootSubset.boundaryRoots_card]
    exact RootSubset.ncard_upper_boundary n hthree vertex target htarget
  exact (RootSubset.full n).nonzero_on upper (spline n hthree vertex)
    (length n hthree vertex) (homogeneous n hthree vertex) (support n hthree vertex) hcard
    vertex (fun invariant hinvariant =>
      RootSubset.eq_on_upper n hthree vertex invariant hinvariant)
    (diagonal n hthree vertex) current habove

/-- The exact Schubert support is its full Bruhat upper ideal. -/
theorem support_exact (vertex current : DihedralGroup n) :
    (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current ≠ 0 ↔
      BruhatLE n hthree vertex current := by
  constructor
  · intro hnonzero
    by_contra hnot
    exact hnonzero (support n hthree vertex current hnot)
  · exact nonzero_above n hthree vertex current

/-- Every upper-ideal evaluation is a nonzero scalar times its outgoing boundary product. -/
theorem localized (vertex current : DihedralGroup n)
    (habove : BruhatLE n hthree vertex current) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧
      (spline n hthree vertex : DihedralGroup n → CoordinatePolynomial) current =
        MvPolynomial.C scalar * (RootSubset.full n).boundaryProduct
          {target | BruhatLE n hthree vertex target} current := by
  obtain ⟨scalar, hscalar⟩ := (RootSubset.full n).localized
    {target | BruhatLE n hthree vertex target} (spline n hthree vertex)
    (length n hthree vertex) (homogeneous n hthree vertex) (support n hthree vertex) current
    (by
      rw [RootSubset.boundaryRoots_card]
      exact RootSubset.ncard_upper_boundary n hthree vertex current habove)
  refine ⟨scalar, ?_, hscalar⟩
  intro hzero
  apply nonzero_above n hthree vertex current habove
  simp [hscalar, hzero]

end Schubert.DihedralSplines.SchubertSpline
