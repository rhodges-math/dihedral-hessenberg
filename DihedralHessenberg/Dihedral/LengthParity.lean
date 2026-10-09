import DihedralHessenberg.Dihedral.RootReflectionVectors
import DihedralHessenberg.Dihedral.LengthCount

/-! # Rotation parity and reflection length -/

namespace Schubert.Dihedral

private theorem parity_rotation (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (coordinate : ZMod n) :
    (coxeterSystem n hthree).lengthParity (DihedralGroup.r coordinate) = 1 := by
  have hfirst : (coxeterSystem n hthree).lengthParity (DihedralGroup.r 1) = 1 := by
    have hpair : DihedralGroup.sr (0 : ZMod n) * DihedralGroup.sr 1 = DihedralGroup.r 1 := by
      rw [DihedralGroup.sr_mul_sr, sub_zero]
    rw [← hpair]
    change (coxeterSystem n hthree).lengthParity
      (simpleReflection n 0 * simpleReflection n 1) = 1
    rw [map_mul, ← coxeterSystem_simple n hthree 0, ← coxeterSystem_simple n hthree 1]
    simp only [CoxeterSystem.lengthParity_simple]
    decide
  have hpower : (DihedralGroup.r (1 : ZMod n)) ^ coordinate.val =
      DihedralGroup.r coordinate := by
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  rw [← hpower, map_pow, hfirst, one_pow]

/-- Rotations have even canonical Coxeter length. -/
theorem even_length_rotation (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (coordinate : ZMod n) : Even (length n hthree (DihedralGroup.r coordinate)) := by
  have hparity := parity_rotation n hthree coordinate
  rw [CoxeterSystem.lengthParity_eq_ofAdd_length] at hparity
  have hzero : ((length n hthree (DihedralGroup.r coordinate) : ℕ) : ZMod 2) = 0 :=
    congrArg Multiplicative.toAdd hparity
  exact ZMod.natCast_eq_zero_iff_even.mp hzero

/-- Odd canonical length characterizes the reflections of positive root vectors. -/
theorem positiveReflection_iff_odd (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (element : DihedralGroup n) :
    (∃ alpha : PositiveRoot n, alpha.reflection = element) ↔ Odd (length n hthree element) := by
  constructor
  · rintro ⟨alpha, rfl⟩
    exact (alpha.isReflection hthree).odd_length
  · intro hodd
    cases element with
    | r coordinate =>
      have heven := even_length_rotation n hthree coordinate
      rw [Nat.even_iff] at heven
      rw [Nat.odd_iff] at hodd
      omega
    | sr coordinate =>
      obtain ⟨index, hindex⟩ := exists_rootReflection_eq_sr n hthree coordinate
      exact ⟨positiveRootEquiv n index, (PositiveRoot.reflection_equiv n index).trans hindex⟩

/-- Opposite-parity vertices in a bounded length ball have the stated exact cardinality. -/
theorem card_parity_ball (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (degree parity : ℕ) (hdegree : degree < n) (hparity : parity < 2) :
    (Finset.univ.filter fun vertex : DihedralGroup n =>
      length n hthree vertex ≤ degree ∧ length n hthree vertex % 2 ≠ parity).card =
        degree + if degree % 2 ≠ parity then 1 else 0 := by
  classical
  induction degree with
  | zero =>
    have hset : (Finset.univ.filter fun vertex : DihedralGroup n =>
        length n hthree vertex ≤ 0 ∧ length n hthree vertex % 2 ≠ parity) =
        if 0 ≠ parity then
          Finset.univ.filter (fun vertex : DihedralGroup n => length n hthree vertex = 0)
        else ∅ := by
      ext vertex
      by_cases hzero : length n hthree vertex = 0
      · by_cases hchoice : 0 ≠ parity <;> simp [hzero, hchoice]
      · by_cases hchoice : 0 ≠ parity <;> simp [hzero, hchoice]
    rw [hset]
    split_ifs <;> simp only [card_length_eq_zero, Finset.card_empty, Nat.zero_add]
  | succ degree ih =>
    have hprevious := ih (by omega)
    let previous := Finset.univ.filter fun vertex : DihedralGroup n =>
      length n hthree vertex ≤ degree ∧ length n hthree vertex % 2 ≠ parity
    let layer := if (degree + 1) % 2 ≠ parity then
      Finset.univ.filter (fun vertex : DihedralGroup n => length n hthree vertex = degree + 1)
      else ∅
    have hset : (Finset.univ.filter fun vertex : DihedralGroup n =>
        length n hthree vertex ≤ degree + 1 ∧ length n hthree vertex % 2 ≠ parity) =
          previous ∪ layer := by
      ext vertex
      dsimp only [previous, layer]
      split_ifs <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union, Finset.notMem_empty, or_false] <;> omega
    have hdisjoint : Disjoint previous layer := by
      apply Finset.disjoint_left.mpr
      intro vertex hfirst hsecond
      have hfirstLength := (Finset.mem_filter.mp hfirst).2.1
      dsimp only [layer] at hsecond
      split_ifs at hsecond
      · have hsecondLength := (Finset.mem_filter.mp hsecond).2
        omega
      · exact Finset.notMem_empty vertex hsecond
    rw [hset, Finset.card_union_of_disjoint hdisjoint]
    change previous.card + layer.card = _
    change previous.card = degree + if degree % 2 ≠ parity then 1 else 0 at hprevious
    rw [hprevious]
    dsimp only [layer]
    split_ifs <;>
      (try rw [card_length_eq_of_positive_lt (degree + 1) (by omega) hdegree]) <;>
      (try rw [Finset.card_empty]) <;> omega

/-- Both canonical length-parity classes have exactly n elements. -/
theorem card_parity_all (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (parity : ℕ) (hparity : parity < 2) :
    (Finset.univ.filter fun vertex : DihedralGroup n =>
      length n hthree vertex % 2 ≠ parity).card = n := by
  classical
  let previous := Finset.univ.filter fun vertex : DihedralGroup n =>
    length n hthree vertex ≤ n - 1 ∧ length n hthree vertex % 2 ≠ parity
  let layer := if n % 2 ≠ parity then
    Finset.univ.filter (fun vertex : DihedralGroup n => length n hthree vertex = n) else ∅
  have hset : (Finset.univ.filter fun vertex : DihedralGroup n =>
      length n hthree vertex % 2 ≠ parity) = previous ∪ layer := by
    ext vertex
    have hbound := length_le_polygon_parameter n hthree vertex
    dsimp only [previous, layer]
    split_ifs <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.notMem_empty, or_false] <;> omega
  have hdisjoint : Disjoint previous layer := by
    apply Finset.disjoint_left.mpr
    intro vertex hfirst hsecond
    have hfirstLength := (Finset.mem_filter.mp hfirst).2.1
    dsimp only [layer] at hsecond
    split_ifs at hsecond
    · have hsecondLength := (Finset.mem_filter.mp hsecond).2
      omega
    · exact Finset.notMem_empty vertex hsecond
  rw [hset, Finset.card_union_of_disjoint hdisjoint]
  change previous.card + layer.card = n
  have hprevious := card_parity_ball n hthree (n - 1) parity (by omega) hparity
  change previous.card = n - 1 + if (n - 1) % 2 ≠ parity then 1 else 0 at hprevious
  rw [hprevious]
  dsimp only [layer]
  split_ifs <;> (try rw [card_length_eq_n]) <;> (try rw [Finset.card_empty]) <;> omega

end Schubert.Dihedral
