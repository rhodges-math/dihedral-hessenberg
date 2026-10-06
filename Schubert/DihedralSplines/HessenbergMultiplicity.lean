import Schubert.DihedralSplines.HessenbergMiddle

/-! # Complete multiplicities of the Hessenberg length distribution -/

namespace Schubert.DihedralSplines.HessenbergSpace

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- The H-length fibers have multiplicity one at the endpoints, two away from
 the middle, and the parity-dependent middle multiplicities. -/
theorem card_length_eq_piecewise (ideal : HessenbergSpace n hthree) (degree : ℕ) :
    (Finset.univ.filter fun element : DihedralGroup n => ideal.length element = degree).card =
      if ideal.roots.card < degree then 0 else
      if degree = 0 ∨ degree = ideal.roots.card then 1 else
      if degree < ideal.roots.card / 2 ∨ ideal.roots.card - ideal.roots.card / 2 < degree
        then 2 else
      if Even ideal.roots.card then 2 * n - 2 * ideal.roots.card + 2
        else n - ideal.roots.card + 2 := by
  classical
  have hminimum := ideal.two_le_card
  have hmaximum := ideal.card_le
  by_cases hout : ideal.roots.card < degree
  · rw [ite_eq_left hout]
    have hempty : (Finset.univ.filter fun element : DihedralGroup n =>
        ideal.length element = degree) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro element hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hbound := ideal.length_le_card_roots element
      omega
    rw [hempty, Finset.card_empty]
  rw [ite_eq_right hout]
  by_cases hend : degree = 0 ∨ degree = ideal.roots.card
  · rw [ite_eq_left hend]
    rcases hend with rfl | rfl
    · exact ideal.card_length_eq_zero
    · exact ideal.card_length_eq_card_roots
  rw [ite_eq_right hend]
  have hpositive : 0 < degree := by omega
  have hdegree : degree < ideal.roots.card := by omega
  have hhalf : 2 * (ideal.roots.card / 2) ≤ ideal.roots.card := by omega
  by_cases houter : degree < ideal.roots.card / 2 ∨
      ideal.roots.card - ideal.roots.card / 2 < degree
  · rw [ite_eq_left houter]
    rcases houter with hlow | hhigh
    · exact ideal.card_length_eq_of_positive_lt_half _ hhalf degree hpositive hlow
    · rw [ideal.card_length_eq_card_complementary_length degree (by omega)]
      exact ideal.card_length_eq_of_positive_lt_half _ hhalf _ (by omega) (by omega)
  rw [ite_eq_right houter]
  by_cases heven : Even ideal.roots.card
  · rw [ite_eq_left heven]
    have hmod := Nat.even_iff.mp heven
    have hcard : ideal.roots.card = 2 * (ideal.roots.card / 2) := by omega
    have hmiddle : degree = ideal.roots.card / 2 := by omega
    rw [hmiddle, ideal.card_length_eq_middle_of_even _ hcard]
    omega
  · rw [ite_eq_right heven]
    have hmod := Nat.not_even_iff.mp heven
    have hcard : ideal.roots.card = 2 * (ideal.roots.card / 2) + 1 := by omega
    have hmiddle := ideal.card_length_eq_middle_of_odd _ hcard
    have hdegrees : degree = ideal.roots.card / 2 ∨ degree = ideal.roots.card / 2 + 1 := by
      omega
    rcases hdegrees with rfl | rfl
    · rw [hmiddle.1]
      omega
    · rw [hmiddle.2]
      omega

end Schubert.DihedralSplines.HessenbergSpace
