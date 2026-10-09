import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Multiplicities of positive weights in a truncated degree sum -/

namespace Schubert.FiniteGroupCharacters

open scoped BigOperators

/-- Positive weights in a degree, with a zero-weight contribution in even degree. -/
def weightPiece {A : Type*} [AddCommMonoid A] (zeroWeight : A) (function : ℕ → A)
    (degree : ℕ) : A :=
  (∑ index : Fin ((degree + 1) / 2), function (degree - 2 * index.val)) +
    if Even degree then zeroWeight else 0

/-- Degree zero has only the zero-weight contribution. -/
@[simp] theorem weightPiece_zero {A : Type*} [AddCommMonoid A] (zeroWeight : A)
    (function : ℕ → A) : weightPiece zeroWeight function 0 = zeroWeight := by
  simp [weightPiece]

/-- Increasing the degree by two inserts exactly the new highest positive weight. -/
theorem weightPiece_step {A : Type*} [AddCommMonoid A] (zeroWeight : A)
    (function : ℕ → A) (degree : ℕ) :
    weightPiece zeroWeight function (degree + 2) =
      function (degree + 2) + weightPiece zeroWeight function degree := by
  have hhalf : (degree + 2 + 1) / 2 = (degree + 1) / 2 + 1 := by omega
  have heven : Even (degree + 2) ↔ Even degree := by
    rw [Nat.even_iff, Nat.even_iff]
    omega
  unfold weightPiece
  simp only [heven]
  rw [Fin.sum_univ_eq_sum_range (fun index => function (degree + 2 - 2 * index)),
    Fin.sum_univ_eq_sum_range (fun index => function (degree - 2 * index)), hhalf,
    Finset.sum_range_succ']
  have hsum : (∑ index ∈ Finset.range ((degree + 1) / 2),
      function (degree + 2 - 2 * (index + 1))) =
      ∑ index ∈ Finset.range ((degree + 1) / 2), function (degree - 2 * index) := by
    apply Finset.sum_congr rfl
    intro index _
    congr 1
    omega
  rw [hsum]
  simp only [mul_zero, Nat.sub_zero]
  ac_rfl

/-- Adjacent degrees contain each positive weight once and the zero weight once. -/
theorem weightPiece_adjacent {A : Type*} [AddCommMonoid A] (zeroWeight : A)
    (function : ℕ → A) (degree : ℕ) :
    weightPiece zeroWeight function (degree + 1) + weightPiece zeroWeight function degree =
      zeroWeight + ∑ index ∈ Finset.range (degree + 1), function (index + 1) := by
  induction degree with
  | zero => simp [weightPiece, add_comm]
  | succ degree ih =>
    rw [show degree + 1 + 1 = degree + 2 by omega, weightPiece_step]
    calc
      function (degree + 2) + weightPiece zeroWeight function degree +
          weightPiece zeroWeight function (degree + 1) =
        function (degree + 2) +
          (weightPiece zeroWeight function (degree + 1) +
            weightPiece zeroWeight function degree) := by ac_rfl
      _ = function (degree + 2) +
          (zeroWeight + ∑ index ∈ Finset.range (degree + 1), function (index + 1)) := by rw [ih]
      _ = _ := by
        conv_rhs => rw [show degree + 2 = (degree + 1) + 1 by omega, Finset.sum_range_succ]
        ac_rfl

/-- The doubled lower-degree sum has triangular positive-weight multiplicities. -/
theorem weightPiece_triangle {A : Type*} [AddCommMonoid A] (zeroWeight : A)
    (function : ℕ → A) (height : ℕ) :
    weightPiece zeroWeight function (height + 1) +
        2 • (∑ degree ∈ Finset.range height, weightPiece zeroWeight function (degree + 1)) =
      height • zeroWeight +
        ∑ index ∈ Finset.range (height + 1), (height + 1 - index) • function (index + 1) := by
  induction height with
  | zero => simp [weightPiece]
  | succ height ih =>
    have hweights :
        (∑ index ∈ Finset.range (height + 1),
          (height + 1 - index) • function (index + 1)) +
          (∑ index ∈ Finset.range (height + 2), function (index + 1)) =
        ∑ index ∈ Finset.range (height + 2), (height + 2 - index) • function (index + 1) := by
      rw [Finset.sum_range_succ (fun index => function (index + 1)) (height + 1),
        Finset.sum_range_succ
          (fun index => (height + 2 - index) • function (index + 1)) (height + 1)]
      simp only [show height + 2 - (height + 1) = 1 by omega, one_smul]
      rw [← add_assoc, ← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro index hindex
      have hbound := Finset.mem_range.mp hindex
      rw [show height + 1 + 1 - index = (height + 1 - index) + 1 by omega, add_smul,
        one_smul]
    rw [Finset.sum_range_succ, smul_add, show height + 1 + 1 = height + 2 by omega]
    calc
      weightPiece zeroWeight function (height + 2) +
          (2 • (∑ degree ∈ Finset.range height,
            weightPiece zeroWeight function (degree + 1)) +
            2 • weightPiece zeroWeight function (height + 1)) =
        (weightPiece zeroWeight function (height + 1) +
          2 • (∑ degree ∈ Finset.range height,
            weightPiece zeroWeight function (degree + 1))) +
          (weightPiece zeroWeight function (height + 2) +
            weightPiece zeroWeight function (height + 1)) := by
        simp only [two_smul]
        ac_rfl
      _ = (height • zeroWeight +
          ∑ index ∈ Finset.range (height + 1),
            (height + 1 - index) • function (index + 1)) +
          (zeroWeight + ∑ index ∈ Finset.range (height + 2), function (index + 1)) := by
        rw [ih, weightPiece_adjacent zeroWeight function (height + 1)]
      _ = _ := by rw [add_smul, one_smul, ← hweights]; ac_rfl

/-- Positive-weight multiplicities in the doubled degree interval are triangular. -/
theorem weightPiece_multiplicity {A : Type*} [AddCommMonoid A] (zeroWeight : A)
    (function : ℕ → A) (height : ℕ) (hheight : 1 ≤ height) :
    weightPiece zeroWeight function height +
        2 • (∑ degree ∈ Finset.Ico 1 height, weightPiece zeroWeight function degree) =
      (height - 1) • zeroWeight +
        ∑ index ∈ Finset.Icc 1 height, (height + 1 - index) • function index := by
  have htriangle := weightPiece_triangle zeroWeight function (height - 1)
  have hsucc : height - 1 + 1 = height := by omega
  rw [hsucc] at htriangle
  have hleft : (∑ degree ∈ Finset.Ico 1 height, weightPiece zeroWeight function degree) =
      ∑ degree ∈ Finset.range (height - 1), weightPiece zeroWeight function (degree + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro degree _
    rw [add_comm]
  have hright : (∑ index ∈ Finset.Icc 1 height,
      (height + 1 - index) • function index) =
      ∑ index ∈ Finset.range height, (height - index) • function (index + 1) := by
    have hinterval : Finset.Icc 1 height = Finset.Ico 1 (height + 1) := by
      ext index
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro index _
    rw [add_comm 1 index, show height + 1 - (index + 1) = height - index by omega]
  rw [hleft, hright]
  exact htriangle

end Schubert.FiniteGroupCharacters
