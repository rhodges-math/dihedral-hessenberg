import DihedralHessenberg.Paper.HessenbergDegreeThreshold
import DihedralHessenberg.Paper.HessenbergExtremes
import DihedralHessenberg.Dihedral.LengthCount
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Low and extremal Hessenberg length fibers

Below half the size of H, the H-degree fibers are canonical length fibers. Thus
their sizes are one in degree zero and two in each positive degree below that half.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- Exactly one vertex has H-length zero. -/
theorem card_length_eq_zero (ideal : HessenbergSpace n hthree) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = 0).card = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.length element = 0) = {1} := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ideal.length_eq_zero_iff element
  rw [hfilter, Finset.card_singleton]

/-- Exactly one vertex has H-length equal to |H|. -/
theorem card_length_eq_card_roots (ideal : HessenbergSpace n hthree) :
    (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.length element = ideal.roots.card).card = 1 := by
  classical
  have hfilter : (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.length element = ideal.roots.card) =
      {(coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)} := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ideal.length_eq_card_roots_iff element
  rw [hfilter, Finset.card_singleton]

/-- Exactly two vertices have each positive H-length below h when |H| is at least 2h. -/
theorem card_length_eq_of_positive_lt_half (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hhalf : 2 * half ≤ ideal.roots.card) (degree : ℕ)
    (hpositive : 0 < degree) (hdegree : degree < half) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = degree).card =
      2 := by
  classical
  have hfilter : (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.length element = degree) =
      (Finset.univ.filter fun element : DihedralGroup n =>
        Schubert.Dihedral.length n hthree element = degree) := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ideal.length_eq_coxeter_below_half half hhalf degree hdegree element
  rw [hfilter]
  have hcard := ideal.card_le
  exact Schubert.Dihedral.card_length_eq_of_positive_lt degree hpositive (by omega)

/-- There are exactly 2h-1 vertices of H-length below h. -/
theorem card_length_lt_half (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hpositive : 0 < half) (hhalf : 2 * half ≤ ideal.roots.card) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element < half).card =
      2 * half - 1 := by
  classical
  have hfiber := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (DihedralGroup n)) (Finset.range half) ideal.length
  simp only [Finset.mem_range] at hfiber
  rw [← hfiber]
  have hsucc : half = (half - 1) + 1 := by omega
  rw [hsucc, Finset.sum_range_succ', ideal.card_length_eq_zero]
  have hconstant : ∑ degree ∈ Finset.range (half - 1),
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = degree + 1).card =
      2 * (half - 1) := by
    calc
      _ = ∑ _degree ∈ Finset.range (half - 1), 2 := by
        apply Finset.sum_congr rfl
        intro degree hdegree
        exact ideal.card_length_eq_of_positive_lt_half half hhalf (degree + 1)
          (by omega) (by simp only [Finset.mem_range] at hdegree; omega)
      _ = _ := by simp [mul_comm]
  rw [hconstant]
  omega

end Schubert.DihedralSplines.HessenbergSpace
