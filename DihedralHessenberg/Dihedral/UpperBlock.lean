import DihedralHessenberg.Dihedral.AscentNormal
import DihedralHessenberg.Dihedral.RootBlock
import DihedralHessenberg.Dihedral.LengthParity
import DihedralHessenberg.Dihedral.RankTwoBruhat

/-! # Alternating blocks and upper ideals in the dihedral order -/

noncomputable section

open scoped Classical

namespace Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

omit [NeZero n] in
/-- A bounded alternating block has one vertex for each prefix length. -/
theorem alternatingBlock_card (vertex : DihedralGroup n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + 1 ≤ n) :
    (alternatingBlock vertex alpha beta half).card = 2 * half + 2 := by
  classical
  rw [alternatingBlock, Finset.card_image_of_injOn, Finset.card_range]
  intro first hfirst second hsecond heq
  have hfirstBound := Finset.mem_range.mp hfirst
  have hsecondBound := Finset.mem_range.mp hsecond
  have hproduct := mul_left_cancel heq
  have hlength := congrArg (length n hthree) hproduct
  rw [PositiveRoot.alternating_length alpha beta hpair first (by omega),
    PositiveRoot.alternating_length alpha beta hpair second (by omega)] at hlength
  exact hlength

/-- A proper Bruhat upper ideal contains twice the remaining distance to the longest element. -/
theorem card_upper (vertex : DihedralGroup n) (hshort : length n hthree vertex < n) :
    (Finset.univ.filter fun target : DihedralGroup n => BruhatLE n hthree vertex target).card =
      2 * (n - length n hthree vertex) := by
  classical
  let : NeZero n := ⟨by omega⟩
  let degree := length n hthree vertex
  let ball := Finset.univ.filter fun target : DihedralGroup n => length n hthree target ≤ degree
  let first := Finset.univ.filter fun target : DihedralGroup n =>
    length n hthree target ≤ degree ∧ length n hthree target % 2 ≠ 0
  let second := Finset.univ.filter fun target : DihedralGroup n =>
    length n hthree target ≤ degree ∧ length n hthree target % 2 ≠ 1
  have hsplit : ball = first ∪ second := by
    ext target
    simp only [ball, first, second, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    have hparity := Nat.mod_lt (length n hthree target) (by decide : 0 < 2)
    omega
  have hdisjoint : Disjoint first second := by
    apply Finset.disjoint_left.mpr
    intro target hfirst hsecond
    have hfirstParity := (Finset.mem_filter.mp hfirst).2.2
    have hsecondParity := (Finset.mem_filter.mp hsecond).2.2
    have hparity := Nat.mod_lt (length n hthree target) (by decide : 0 < 2)
    omega
  have hfirst := card_parity_ball n hthree degree 0 hshort (by decide)
  have hsecond := card_parity_ball n hthree degree 1 hshort (by decide)
  have hball : ball.card = 2 * degree + 1 := by
    rw [hsplit, Finset.card_union_of_disjoint hdisjoint]
    change first.card = degree + if degree % 2 ≠ 0 then 1 else 0 at hfirst
    change second.card = degree + if degree % 2 ≠ 1 then 1 else 0 at hsecond
    rw [hfirst, hsecond]
    have hparity := Nat.mod_lt degree (by decide : 0 < 2)
    split_ifs <;> omega
  have hvertex : vertex ∈ ball := by simp only [ball, Finset.mem_filter, Finset.mem_univ,
    true_and, degree, le_refl]
  have hupper : (Finset.univ.filter fun target : DihedralGroup n =>
      BruhatLE n hthree vertex target) = Finset.univ \ (ball.erase vertex) := by
    ext target
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_erase, ball, ne_eq, bruhatLE_iff_eq_or_length_lt]
    change vertex = target ∨ degree < length n hthree target ↔
      ¬(target ≠ vertex ∧ length n hthree target ≤ degree)
    rw [not_and_or, not_not, not_le]
    exact or_congr_left eq_comm
  rw [hupper, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    DihedralGroup.card, Finset.card_erase_of_mem hvertex, hball]
  dsimp only [degree]
  omega

omit [NeZero n] in
/-- A high-half right ascent enumerates its entire Bruhat upper ideal as an alternating block. -/
theorem alternatingBlock_upper (vertex : DihedralGroup n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hascent : length n hthree (vertex * alpha.reflection) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1) :
    (alternatingBlock vertex alpha beta (n - length n hthree vertex - 1) :
      Set (DihedralGroup n)) = {target | BruhatLE n hthree vertex target} := by
  classical
  let : NeZero n := ⟨by omega⟩
  have hbound := length_le_polygon_parameter n hthree (vertex * alpha.reflection)
  have hshort : length n hthree vertex < n := by omega
  have hpositive : 0 < length n hthree vertex := by omega
  have hcardBlock := alternatingBlock_card vertex alpha beta hpair
    (n - length n hthree vertex - 1) (by omega)
  have hcardUpper := card_upper vertex hshort
  have hsubset : alternatingBlock vertex alpha beta (n - length n hthree vertex - 1) ⊆
      Finset.univ.filter fun target : DihedralGroup n => BruhatLE n hthree vertex target := by
    intro target htarget
    obtain ⟨position, hposition, rfl⟩ :=
      (mem_alternatingBlock vertex target alpha beta _).mp htarget
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hzero : position = 0
    · subst position
      rw [PositiveRoot.alternating_zero, mul_one]
      exact bruhatLE_refl n hthree vertex
    · apply bruhatLE_of_length_lt n hthree
      rw [right_ascent_prefix_length alpha beta hpair vertex hpositive hascent position (by omega)]
      omega
  have heq := Finset.eq_of_subset_of_card_le hsubset (by rw [hcardUpper, hcardBlock]; omega)
  rw [heq]
  ext target
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

end Schubert.Dihedral
