import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Dimensions of lower-half frequency multiplicity sums -/

namespace Schubert.FiniteGroupCharacters

open scoped BigOperators

private theorem threshold_sum (size cut : ℕ) :
    (∑ index : Fin size, if cut ≤ index.val then 1 else 0) = size - cut := by
  induction size with
  | zero => simp
  | succ size induction =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, induction]
    split_ifs <;> omega

private theorem strict_sum (size height : ℕ) :
    (∑ index : Fin size, if height < index.val + 1 then 1 else 0) = size - height := by
  have hiff (index : Fin size) : height < index.val + 1 ↔ height ≤ index.val := by omega
  simp only [hiff]
  exact threshold_sum size height

private theorem inclusive_sum (size height : ℕ) (hpositive : 1 ≤ height) :
    (∑ index : Fin size, if height ≤ index.val + 1 then 1 else 0) = size - (height - 1) := by
  have hiff (index : Fin size) : height ≤ index.val + 1 ↔ height - 1 ≤ index.val := by omega
  simp only [hiff]
  exact threshold_sum size (height - 1)

private theorem middle_sum (size height : ℕ) (hpositive : 1 ≤ height) :
    (∑ index : Fin size, if index.val + 1 = height then 1
      else if height < index.val + 1 then 2 else 0) =
        (size - (height - 1)) + (size - height) := by
  have hpoint (index : Fin size) :
      (if index.val + 1 = height then 1 else if height < index.val + 1 then 2 else 0) =
        (if height ≤ index.val + 1 then 1 else 0) +
          (if height < index.val + 1 then 1 else 0) := by
    split_ifs <;> omega
  simp only [hpoint, Finset.sum_add_distrib]
  rw [inclusive_sum size height hpositive, strict_sum]

private theorem twice_sum (size height : ℕ) (hpositive : 1 ≤ height) :
    (∑ index : Fin size, if height ≤ index.val + 1 then 2 else 0) =
      2 * (size - (height - 1)) := by
  have hpoint (index : Fin size) : (if height ≤ index.val + 1 then 2 else 0) =
      2 * (if height ≤ index.val + 1 then 1 else 0) := by split_ifs <;> rfl
  simp only [hpoint, ← Finset.mul_sum]
  rw [inclusive_sum size height hpositive]

/-- The even middle-frequency multiplicities have their full left dimension. -/
theorem even_left_budget (parameter height : ℕ) (hpositive : 1 ≤ height)
    (hbound : 2 * height < parameter) :
    2 * (∑ index : Fin ((parameter - 1) / 2),
      if index.val + 1 = height then 1 else if height < index.val + 1 then 2 else 0) +
      2 + (if Even parameter then 2 else 0) = 2 * parameter - 4 * height + 2 := by
  rw [middle_sum _ _ hpositive]
  by_cases heven : Even parameter
  · rw [ite_eq_left heven]
    have hparity := Nat.even_iff.mp heven
    omega
  · rw [ite_eq_right heven]
    have hparity : parameter % 2 ≠ 0 := by simpa only [Nat.even_iff] using heven
    omega

/-- The even middle-frequency multiplicities have their full right dimension. -/
theorem even_right_budget (parameter height : ℕ) (hpositive : 1 ≤ height)
    (hbound : 2 * height < parameter) :
    2 * (∑ index : Fin ((parameter - 1) / 2),
      if height ≤ index.val + 1 then 2 else 0) +
      (if Even parameter then 2 else 0) = 2 * parameter - 4 * height + 2 := by
  rw [twice_sum _ _ hpositive]
  by_cases heven : Even parameter
  · rw [ite_eq_left heven]
    have hparity := Nat.even_iff.mp heven
    omega
  · rw [ite_eq_right heven]
    have hparity : parameter % 2 ≠ 0 := by simpa only [Nat.even_iff] using heven
    omega

/-- The odd middle-frequency multiplicities have their full left dimension. -/
theorem odd_left_budget (parameter height : ℕ) (hpositive : 1 ≤ height)
    (hbound : 2 * height < parameter) :
    2 * (∑ index : Fin ((parameter - 1) / 2), if height < index.val + 1 then 1 else 0) +
      2 + (if Even parameter then 1 else 0) = parameter - 2 * height + 1 := by
  rw [strict_sum]
  by_cases heven : Even parameter
  · rw [ite_eq_left heven]
    have hparity := Nat.even_iff.mp heven
    omega
  · rw [ite_eq_right heven]
    have hparity : parameter % 2 ≠ 0 := by simpa only [Nat.even_iff] using heven
    omega

/-- The odd middle-frequency multiplicities have their full right dimension. -/
theorem odd_right_budget (parameter height : ℕ) (hpositive : 1 ≤ height)
    (hbound : 2 * height < parameter) :
    2 * (∑ index : Fin ((parameter - 1) / 2), if height ≤ index.val + 1 then 1 else 0) +
      (if Even parameter then 1 else 0) = parameter - 2 * height + 1 := by
  rw [inclusive_sum _ _ hpositive]
  by_cases heven : Even parameter
  · rw [ite_eq_left heven]
    have hparity := Nat.even_iff.mp heven
    omega
  · rw [ite_eq_right heven]
    have hparity : parameter % 2 ≠ 0 := by simpa only [Nat.even_iff] using heven
    omega

end Schubert.FiniteGroupCharacters
