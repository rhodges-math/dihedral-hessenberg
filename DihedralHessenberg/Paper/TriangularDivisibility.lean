import DihedralHessenberg.Dihedral.BruhatOrder
import DihedralHessenberg.Dihedral.RootPolynomialAction
import DihedralHessenberg.Paper.Grading
import DihedralHessenberg.Paper.HessenbergInversions
import DihedralHessenberg.Splines.HomogeneousDivisibility

/-! # Hessenberg diagonal divisibility

Descending right reflections in a Hessenberg graph force every corresponding root label
to divide a residual value. The common-action root forms are pairwise relatively prime,
and their homogeneous product degree is the number of selected right inversions.
-/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- A diagonal of minimal inversion degree divides every spline value vanishing below it. -/
theorem hessenberg_diagonal_dvd_of_degree_bound
    (diagonal value : HessenbergSpline ideal) (vertex : DihedralGroup n)
    (hdiagonalZero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
      (diagonal : DihedralGroup n → CoordinatePolynomial) lower = 0)
    (hvalueZero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
      (value : DihedralGroup n → CoordinatePolynomial) lower = 0)
    (hnonzero : (diagonal : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hdegree : ((diagonal : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
      ideal.length vertex) :
    (diagonal : DihedralGroup n → CoordinatePolynomial) vertex ∣
      (value : DihedralGroup n → CoordinatePolynomial) vertex := by
  classical
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let indices := ideal.inversions vertex
  let labels := fun index => polynomialAction n vertex (rootPolynomial n index)
  have hdivides (spline : HessenbergSpline ideal)
      (hzero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
        (spline : DihedralGroup n → CoordinatePolynomial) lower = 0)
      (index : PositiveRootIndex n) (hindex : index ∈ indices) :
      labels index ∣ (spline : DihedralGroup n → CoordinatePolynomial) vertex := by
    have hmembership := (ideal.mem_inversions vertex index).mp hindex
    have hlength := hmembership.2
    have hbruhat := (rootReflection_bruhatLE_mul_right_iff n hthree index vertex).2 hlength
    have hne : vertex * rootReflection index ≠ vertex := by
      intro heq
      rw [heq] at hlength
      exact (lt_irrefl _) hlength
    exact (hessenbergGraph ideal).label_dvd_of_target_eq_zero spline
      (vertex, ⟨index, hmembership.1⟩) (labels index) rfl
      (hzero (vertex * rootReflection index) hbruhat hne)
  apply _root_.Schubert.Splines.HomogeneousDivisibility.diagonal_dvd indices labels (fun _ => 1)
  · intro index _
    exact polynomialAction_isHomogeneous n vertex (rootPolynomial_isHomogeneous n index)
  · intro index _
    exact polynomialAction_rootPolynomial_ne_zero n vertex index
  · intro first _ second _ hne
    exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime n vertex first second hne
  · simpa [indices, HessenbergSpace.length] using hdegree
  · exact hnonzero
  · exact hdivides diagonal hdiagonalZero
  · exact hdivides value hvalueZero

end Schubert.DihedralSplines
