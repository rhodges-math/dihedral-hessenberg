import Schubert.DihedralSplines.HessenbergLengthFibers
import Schubert.DihedralSplines.HessenbergDegreeCount

/-! # Middle coefficients of the Hessenberg degree distribution -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

private theorem card_filter_between_partition (ideal : HessenbergSpace n hthree)
    (lower upper : ℕ) (hbound : lower ≤ upper) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element < lower).card +
      (Finset.univ.filter fun element : DihedralGroup n =>
        lower ≤ ideal.length element ∧ ideal.length element ≤ upper).card +
      (Finset.univ.filter fun element : DihedralGroup n => upper < ideal.length element).card =
      2 * n := by
  classical
  have hfirst := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun element : DihedralGroup n => ideal.length element < lower)
  have hsecond := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun element : DihedralGroup n => ¬ideal.length element < lower)
    (fun element => ideal.length element ≤ upper)
  have hcentral : ((Finset.univ.filter fun element : DihedralGroup n =>
      ¬ideal.length element < lower).filter fun element => ideal.length element ≤ upper) =
      (Finset.univ.filter fun element : DihedralGroup n =>
        lower ≤ ideal.length element ∧ ideal.length element ≤ upper) := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hhigh : ((Finset.univ.filter fun element : DihedralGroup n =>
      ¬ideal.length element < lower).filter fun element => ¬ideal.length element ≤ upper) =
      (Finset.univ.filter fun element : DihedralGroup n => upper < ideal.length element) := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hcentral, hhigh] at hsecond
  rw [Finset.card_univ, DihedralGroup.card] at hfirst
  omega

private theorem card_length_gt_complementary_half (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hpositive : 0 < half) (hhalf : 2 * half ≤ ideal.roots.card) :
    (Finset.univ.filter fun element : DihedralGroup n =>
      ideal.roots.card - half < ideal.length element).card = 2 * half - 1 := by
  classical
  have hlow := ideal.card_length_lt_half half hpositive hhalf
  rw [← hlow]
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

/-- An even-sized Hessenberg ideal has middle degree multiplicity 2n-4h+2. -/
theorem card_length_eq_middle_of_even (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half).card =
      2 * n - 4 * half + 2 := by
  classical
  have hminimum := ideal.two_le_card
  have hmaximum := ideal.card_le
  have hpositive : 0 < half := by omega
  have hhalf : 2 * half ≤ ideal.roots.card := hcard.ge
  have hlow := ideal.card_length_lt_half half hpositive hhalf
  have hhigh := card_length_gt_complementary_half ideal half hpositive hhalf
  have hsub : ideal.roots.card - half = half := by omega
  rw [hsub] at hhigh
  have hpartition := card_filter_between_partition ideal half half le_rfl
  have hcentral : (Finset.univ.filter fun element : DihedralGroup n =>
      half ≤ ideal.length element ∧ ideal.length element ≤ half) =
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half) := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hcentral, hlow, hhigh] at hpartition
  omega

/-- An odd-sized Hessenberg ideal has both middle degree multiplicities n-2h+1. -/
theorem card_length_eq_middle_of_odd (ideal : HessenbergSpace n hthree)
    (half : ℕ) (hcard : ideal.roots.card = 2 * half + 1) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half).card =
      n - 2 * half + 1 ∧
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half + 1).card =
      n - 2 * half + 1 := by
  classical
  have hminimum := ideal.two_le_card
  have hmaximum := ideal.card_le
  have hpositive : 0 < half := by omega
  have hhalf : 2 * half ≤ ideal.roots.card := by omega
  have hlow := ideal.card_length_lt_half half hpositive hhalf
  have hhigh := card_length_gt_complementary_half ideal half hpositive hhalf
  have hsub : ideal.roots.card - half = half + 1 := by omega
  rw [hsub] at hhigh
  have hequal := ideal.card_length_eq_card_complementary_length half (by omega)
  rw [hsub] at hequal
  have hpartition := card_filter_between_partition ideal half (half + 1) (by omega)
  have hcentral : (Finset.univ.filter fun element : DihedralGroup n =>
      half ≤ ideal.length element ∧ ideal.length element ≤ half + 1) =
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half) ∪
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half + 1) := by
    ext element
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisjoint : Disjoint
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half)
      (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = half + 1) := by
    apply Finset.disjoint_left.mpr
    intro element hfirst hsecond
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hfirst hsecond
    omega
  rw [hcentral, Finset.card_union_of_disjoint hdisjoint, hlow, hhigh] at hpartition
  omega

end Schubert.DihedralSplines.HessenbergSpace
