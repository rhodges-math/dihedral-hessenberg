import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Pairing opposite weights in a finite interval -/

namespace Schubert.FiniteGroupCharacters

open scoped BigOperators

/-- Odd-degree weights split into opposite pairs. -/
theorem sum_odd_weights {A : Type*} [AddCommMonoid A] (function : ℤ → A) (half : ℕ) :
    ∑ j : Fin (2 * half), function ((2 * half - 1 : ℤ) - 2 * j.val) =
      ∑ j : Fin half, (function ((2 * half - 1 : ℤ) - 2 * j.val) +
        function (-((2 * half - 1 : ℤ) - 2 * j.val))) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => function ((2 * half - 1 : ℤ) - 2 * j)),
    Fin.sum_univ_eq_sum_range (fun j => function ((2 * half - 1 : ℤ) - 2 * j) +
      function (-((2 * half - 1 : ℤ) - 2 * j)))]
  have hsplit : 2 * half = half + half := by omega
  conv_lhs => arg 1; rw [hsplit]
  rw [Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1
  rw [← Finset.sum_range_reflect
    (fun j => function ((2 * half - 1 : ℤ) - 2 * (half + j : ℕ)))]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  congr 1
  rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

/-- Even-degree weights split into opposite pairs and a single zero weight. -/
theorem sum_even_weights {A : Type*} [AddCommMonoid A] (function : ℤ → A) (half : ℕ) :
    ∑ j : Fin (2 * half + 1), function ((2 * half : ℤ) - 2 * j.val) =
      (∑ j : Fin half, (function ((2 * half : ℤ) - 2 * j.val) +
        function (-((2 * half : ℤ) - 2 * j.val)))) + function 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => function ((2 * half : ℤ) - 2 * j)),
    Fin.sum_univ_eq_sum_range (fun j => function ((2 * half : ℤ) - 2 * j) +
      function (-((2 * half : ℤ) - 2 * j)))]
  have hsplit : 2 * half + 1 = half + (half + 1) := by omega
  conv_lhs => arg 1; rw [hsplit]
  rw [Finset.sum_range_add, Finset.sum_range_succ', Finset.sum_add_distrib]
  have hnegative :
      ∑ j ∈ Finset.range half, function ((2 * half : ℤ) - 2 * (half + (j + 1) : ℕ)) =
        ∑ j ∈ Finset.range half, function (-((2 * half : ℤ) - 2 * j)) := by
    rw [← Finset.sum_range_reflect
      (fun j => function ((2 * half : ℤ) - 2 * (half + (j + 1) : ℕ)))]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    congr 1
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hnegative]
  have hzero : (2 * half : ℤ) - 2 * (half + 0 : ℕ) = 0 := by push_cast; ring
  rw [hzero]
  ac_rfl

/-- A homogeneous weight interval pairs opposite weights, retaining zero in even degree. -/
theorem sum_weight_pairs {A : Type*} [AddCommMonoid A] (function : ℤ → A) (degree : ℕ) :
    ∑ j : Fin (degree + 1), function ((degree : ℤ) - 2 * j.val) =
      (∑ j : Fin ((degree + 1) / 2),
        (function ((degree : ℤ) - 2 * j.val) +
          function (-((degree : ℤ) - 2 * j.val)))) +
            if Even degree then function 0 else 0 := by
  by_cases heven : Even degree
  · rw [ite_eq_left heven]
    obtain ⟨half, hhalf⟩ := heven
    have hdegree : degree = 2 * half := by omega
    have hsize : (degree + 1) / 2 = half := by omega
    rw [hsize, hdegree]
    exact sum_even_weights function half
  · rw [ite_eq_right heven, add_zero]
    obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
    have hdegree : degree + 1 = 2 * (half + 1) := by omega
    have hsize : (degree + 1) / 2 = half + 1 := by omega
    have hweight : (degree : ℤ) = 2 * (half + 1 : ℕ) - 1 := by omega
    rw [hsize, hdegree, hweight]
    exact sum_odd_weights function (half + 1)

end Schubert.FiniteGroupCharacters
