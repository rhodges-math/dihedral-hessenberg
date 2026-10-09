import DihedralHessenberg.Paper.TriangularDivisibility
import DihedralHessenberg.Splines.HomogeneousMinimalMultiple

/-! # Homogeneous diagonals of minimal-degree Hessenberg splines -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- The inversion-label product divides a spline value whose descending values vanish. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.inversion_product_dvd [NeZero n]
    (value : HessenbergSpline ideal) (vertex : DihedralGroup n)
    (hzero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
      (value : DihedralGroup n → CoordinatePolynomial) lower = 0) :
    (∏ index ∈ ideal.inversions vertex,
      polynomialAction n vertex (rootPolynomial n index)) ∣
        (value : DihedralGroup n → CoordinatePolynomial) vertex := by
  classical
  apply Finset.prod_dvd_of_isRelPrime
  · intro first _ second _ hne
    exact _root_.Schubert.Dihedral.IndexedRoots.Form.action_coprime n vertex first second hne
  · intro index hindex
    have hmembership := (ideal.mem_inversions vertex index).mp hindex
    have hlength := hmembership.2
    have hbruhat := (rootReflection_bruhatLE_mul_right_iff n hthree index vertex).2 hlength
    have hne : vertex * rootReflection index ≠ vertex := by
      intro heq
      rw [heq] at hlength
      exact (lt_irrefl _) hlength
    exact (hessenbergGraph ideal).label_dvd_of_target_eq_zero value
      (vertex, ⟨index, hmembership.1⟩) _ rfl
      (hzero (vertex * rootReflection index) hbruhat hne)

/-- A nonzero minimal-degree diagonal is homogeneous in its Hessenberg length. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.diagonal_homogeneous
    (value : HessenbergSpline ideal) (vertex : DihedralGroup n)
    (hzero : ∀ lower, BruhatLE n hthree lower vertex → lower ≠ vertex →
      (value : DihedralGroup n → CoordinatePolynomial) lower = 0)
    (hnonzero : (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0)
    (hdegree : ((value : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
      ideal.length vertex) :
    ((value : DihedralGroup n → CoordinatePolynomial) vertex).IsHomogeneous
      (ideal.length vertex) := by
  classical
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply _root_.Schubert.Splines.HomogeneousMultiple.of_dvd_degree_le
    (multiple := (value : DihedralGroup n → CoordinatePolynomial) vertex)
    (divisor := ∏ index ∈ ideal.inversions vertex,
      polynomialAction n vertex (rootPolynomial n index))
  · have hproduct := MvPolynomial.IsHomogeneous.prod (ideal.inversions vertex)
      (fun index => polynomialAction n vertex (rootPolynomial n index)) (fun _ => 1)
      (fun index _ => polynomialAction_isHomogeneous n vertex
        (rootPolynomial_isHomogeneous n index))
    simpa [HessenbergSpace.length] using hproduct
  · exact _root_.Schubert.DihedralSplines.IndexedSpline.inversion_product_dvd ideal value vertex
      hzero
  · exact hnonzero
  · exact hdegree

end Schubert.DihedralSplines
