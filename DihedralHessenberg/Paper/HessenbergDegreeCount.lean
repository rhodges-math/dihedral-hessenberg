import DihedralHessenberg.Paper.HessenbergSymmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Symmetry and total sum of Hessenberg degrees

The longest-element involution pairs complementary H-degrees. In particular the
degree distribution is symmetric and its total sum is n times the size of H.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- Complementary H-degrees occur at equally many vertices. -/
theorem card_length_eq_card_complementary_length (ideal : HessenbergSpace n hthree)
    (degree : ℕ) (hdegree : degree ≤ ideal.roots.card) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = degree).card =
      (Finset.univ.filter fun element : DihedralGroup n =>
        ideal.length element = ideal.roots.card - degree).card := by
  classical
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have hself : top * top = 1 := by
    have hinv : top⁻¹ = top := alternatingWord_top_inv n hthree
    calc
      top * top = top⁻¹ * top := by rw [hinv]
      _ = 1 := inv_mul_cancel _
  apply Finset.card_bij (fun element _ => top * element)
  · intro element hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
    have hsum := ideal.length_alternatingWord_top_mul_add element
    change ideal.length (top * element) + ideal.length element = ideal.roots.card at hsum
    omega
  · intro first _ second _ heq
    exact mul_left_cancel heq
  · intro element hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    refine ⟨top * element, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hsum := ideal.length_alternatingWord_top_mul_add element
      change ideal.length (top * element) + ideal.length element = ideal.roots.card at hsum
      omega
    · rw [← mul_assoc, hself, one_mul]

/-- The total H-length over all vertices is n times the number of roots in H. -/
theorem sum_length (ideal : HessenbergSpace n hthree) :
    ∑ element : DihedralGroup n, ideal.length element = n * ideal.roots.card := by
  classical
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have hsum : (∑ element : DihedralGroup n, ideal.length (top * element)) +
      ∑ element : DihedralGroup n, ideal.length element = 2 * n * ideal.roots.card := by
    rw [← Finset.sum_add_distrib]
    have hconstant : ∀ element, ideal.length (top * element) + ideal.length element =
        ideal.roots.card := ideal.length_alternatingWord_top_mul_add
    simp only [hconstant, Finset.sum_const, Finset.card_univ, DihedralGroup.card, nsmul_eq_mul]
    simp
  have hbijective : Function.Bijective (fun element : DihedralGroup n => top * element) := by
    constructor
    · intro first second heq
      exact mul_left_cancel heq
    · intro element
      exact ⟨top⁻¹ * element, mul_inv_cancel_left _ _⟩
  have hpermuted : (∑ element : DihedralGroup n, ideal.length (top * element)) =
      ∑ element : DihedralGroup n, ideal.length element :=
    hbijective.sum_comp ideal.length
  rw [hpermuted] at hsum
  rw [mul_assoc] at hsum
  omega

end Schubert.DihedralSplines.HessenbergSpace
