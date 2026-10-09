import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Pairing opposite cyclic frequencies -/

namespace Schubert.FiniteGroupCharacters

open scoped BigOperators

private theorem sum_cast {n : ℕ} [NeZero n] {A : Type*} [AddCommMonoid A]
    (function : ZMod n → A) :
    ∑ j : ZMod n, function j = ∑ j ∈ Finset.range n, function (j : ZMod n) := by
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv.symm
  intro j
  congr 1
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => exact (ZMod.natCast_zmod_val j).symm

private theorem cast_opposite {n : ℕ} (j : ℕ) (hbound : j ≤ n) :
    ((n - j : ℕ) : ZMod n) = -(j : ZMod n) := by
  rw [Nat.cast_sub hbound, ZMod.natCast_self, zero_sub]

/-- A sum over an odd cyclic group pairs every nonzero frequency with its opposite. -/
theorem sum_odd_pairs {n : ℕ} [NeZero n] {A : Type*} [AddCommMonoid A]
    (function : ZMod n → A) (half : ℕ) (hsize : n = 2 * half + 1) :
    ∑ j : ZMod n, function j = function 0 +
      ∑ j : Fin half, (function ((j.val + 1 : ℕ) : ZMod n) +
        function (-((j.val + 1 : ℕ) : ZMod n))) := by
  rw [sum_cast]
  rw [Fin.sum_univ_eq_sum_range (fun j => function ((j + 1 : ℕ) : ZMod n) +
    function (-((j + 1 : ℕ) : ZMod n))) half]
  have hsplit : n = (half + half) + 1 := by omega
  conv_lhs => arg 1; rw [hsplit]
  rw [Finset.sum_range_succ', Finset.sum_range_add, Finset.sum_add_distrib]
  have hnegative :
      ∑ j ∈ Finset.range half, function ((half + j + 1 : ℕ) : ZMod n) =
        ∑ j ∈ Finset.range half, function (-((j + 1 : ℕ) : ZMod n)) := by
    rw [← Finset.sum_range_reflect (fun j => function ((half + j + 1 : ℕ) : ZMod n))]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hindex : half + (half - 1 - j) + 1 = n - (j + 1) := by omega
    rw [hindex, cast_opposite _ (by omega)]
  rw [hnegative]
  simp only [Nat.cast_zero]
  ac_rfl

/-- An even cyclic group pairs opposite frequencies and leaves its unique midpoint. -/
theorem sum_even_pairs {n : ℕ} [NeZero n] {A : Type*} [AddCommMonoid A]
    (function : ZMod n → A) (half : ℕ) (hsize : n = 2 * half + 2) :
    ∑ j : ZMod n, function j = function 0 +
      ∑ j : Fin half, (function ((j.val + 1 : ℕ) : ZMod n) +
        function (-((j.val + 1 : ℕ) : ZMod n))) +
          function ((half + 1 : ℕ) : ZMod n) := by
  rw [sum_cast]
  rw [Fin.sum_univ_eq_sum_range (fun j => function ((j + 1 : ℕ) : ZMod n) +
    function (-((j + 1 : ℕ) : ZMod n))) half]
  have hsplit : n = (half + (half + 1)) + 1 := by omega
  conv_lhs => arg 1; rw [hsplit]
  rw [Finset.sum_range_succ', Finset.sum_range_add, Finset.sum_range_succ',
    Finset.sum_add_distrib]
  have hnegative :
      ∑ j ∈ Finset.range half, function ((half + (j + 1) + 1 : ℕ) : ZMod n) =
        ∑ j ∈ Finset.range half, function (-((j + 1 : ℕ) : ZMod n)) := by
    rw [← Finset.sum_range_reflect
      (fun j => function ((half + (j + 1) + 1 : ℕ) : ZMod n))]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    have hindex : half + ((half - 1 - j) + 1) + 1 = n - (j + 1) := by omega
    rw [hindex, cast_opposite _ (by omega)]
  rw [hnegative]
  simp only [Nat.cast_zero, add_zero]
  ac_rfl

/-- Every positive cyclic modulus splits into zero, opposite pairs, and its even midpoint. -/
theorem sum_frequency_pairs {n : ℕ} [NeZero n] {A : Type*} [AddCommMonoid A]
    (function : ZMod n → A) :
    ∑ j : ZMod n, function j = function 0 +
      ∑ j : Fin ((n - 1) / 2), (function ((j.val + 1 : ℕ) : ZMod n) +
        function (-((j.val + 1 : ℕ) : ZMod n))) +
          if Even n then function ((n / 2 : ℕ) : ZMod n) else 0 := by
  have hpositive : 0 < n := NeZero.pos n
  by_cases heven : Even n
  · rw [ite_eq_left heven]
    obtain ⟨half, hhalf⟩ := heven
    have hsize : n = 2 * ((n - 1) / 2) + 2 := by omega
    have hmidpoint : n / 2 = (n - 1) / 2 + 1 := by omega
    rw [hmidpoint]
    exact sum_even_pairs function _ hsize
  · obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
    have hsize : n = 2 * ((n - 1) / 2) + 1 := by omega
    rw [ite_eq_right heven, add_zero]
    exact sum_odd_pairs function _ hsize

end Schubert.FiniteGroupCharacters
