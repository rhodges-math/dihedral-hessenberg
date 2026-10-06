import Schubert.DihedralSplines.DividedDifference
import Schubert.DihedralSplines.Grading
import Schubert.Splines.HomogeneousDivision

/-! # Degree and support of admissible Hessenberg divided differences -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- A divided difference lowers positive homogeneous degree by exactly one. -/
theorem _root_.Schubert.DihedralSplines.IndexedDD.mem_homogeneousPiece
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex)
    (degree : ℕ) (hdegree : value ∈ (hessenbergGraph ideal).homogeneousPiece (degree + 1)) :
    hessenbergDividedDifference ideal value index hedges ∈
      (hessenbergGraph ideal).homogeneousPiece degree := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  intro vertex
  apply polynomial_quotient_isHomogeneous (rootPolynomial_isHomogeneous n index)
    (rootPolynomial_ne_zero n index)
  rw [hessenbergDividedDifference_mul_apply]
  have hdot := _root_.Schubert.DihedralSplines.IndexedSpline.dot_mem_homogeneousPiece ideal
    (rootReflection index) (degree + 1) value hdegree vertex
  simpa only [Nat.add_comm] using (hdegree vertex).sub hdot

/-- A divided difference vanishes where both reflected input vertices vanish. -/
theorem _root_.Schubert.DihedralSplines.IndexedDD.eq_zero_of_pair_eq_zero
    (value : HessenbergSpline ideal) (index : PositiveRootIndex n)
    (hedges : ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 →
      ∃ edgeIndex ∈ ideal.roots,
        vertex * rootReflection edgeIndex = rootReflection index * vertex)
    (vertex : DihedralGroup n)
    (hfirst : (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hsecond : (value : DihedralGroup n → CoordinatePolynomial)
      (rootReflection index * vertex) = 0) :
    (hessenbergDividedDifference ideal value index hedges :
      DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply mul_left_cancel₀ (rootPolynomial_ne_zero n index)
  rw [mul_zero, hessenbergDividedDifference_mul_apply]
  change (value : DihedralGroup n → CoordinatePolynomial) vertex -
    polynomialAction n (rootReflection index)
      ((value : DihedralGroup n → CoordinatePolynomial) ((rootReflection index)⁻¹ * vertex)) = 0
  have hinverse : (rootReflection index)⁻¹ = rootReflection index :=
    inv_eq_of_mul_eq_one_right (rootReflection_mul_self index)
  rw [hinverse, hfirst, hsecond, map_zero, sub_zero]

end Schubert.DihedralSplines
