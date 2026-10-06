import Schubert.Dihedral.ReducedWords

/-! # Reduced alternating words in the dihedral group

Alternating words of length at most n have distinct canonical inversion sequences.
-/

namespace Schubert.Dihedral

/-- The product of an odd alternating word is an alternating reflection word. -/
theorem alternatingWord_odd_wordProd (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (halfLength : ℕ) :
    (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord second first (2 * halfLength + 1)) =
      (simpleReflection n first * simpleReflection n second) ^ halfLength *
        simpleReflection n first := by
  rw [CoxeterSystem.alternatingWord_succ, CoxeterSystem.wordProd_concat,
    CoxeterSystem.prod_alternatingWord_eq_mul_pow]
  have heven : Even (2 * halfLength) := ⟨halfLength, by omega⟩
  simp only [ite_eq_left heven, one_mul, coxeterSystem_simple]
  have hhalf : (2 * halfLength) / 2 = halfLength := by omega
  rw [hhalf]

private theorem initial_inversion_sequence_nodup (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2)
    (hinjective : Function.Injective fun k : Fin n =>
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord second first (2 * k.val + 1)))
    (size : ℕ) (hsize : size ≤ n) :
    (((coxeterSystem n hthree).leftInvSeq
      (CoxeterSystem.alternatingWord first second (2 * n))).take size).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j heq
  have hi : i.val < n := by
    have := i.isLt
    simp only [List.length_take, CoxeterSystem.length_leftInvSeq,
      CoxeterSystem.length_alternatingWord] at this
    omega
  have hj : j.val < n := by
    have := j.isLt
    simp only [List.length_take, CoxeterSystem.length_leftInvSeq,
      CoxeterSystem.length_alternatingWord] at this
    omega
  simp only [List.getElem_take] at heq
  rw [(coxeterSystem n hthree).getElem_leftInvSeq_alternatingWord first second n i.val
      (by omega),
    (coxeterSystem n hthree).getElem_leftInvSeq_alternatingWord first second n j.val
      (by omega)] at heq
  exact Fin.ext (congrArg (fun k : Fin n => k.val) (hinjective (a₁ := ⟨i.val, hi⟩)
    (a₂ := ⟨j.val, hj⟩) heq))

private theorem odd_products_injective (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (hne : first ≠ second) :
    Function.Injective fun k : Fin n =>
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord second first (2 * k.val + 1)) := by
  intro i j heq
  dsimp only at heq
  rw [alternatingWord_odd_wordProd, alternatingWord_odd_wordProd] at heq
  have hcast : (i.val : ZMod n) = (j.val : ZMod n) := by
    fin_cases first <;> fin_cases second
    · exact (hne rfl).elim
    · simpa [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
        DihedralGroup.r_mul_sr] using heq
    · simpa [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
        DihedralGroup.r_mul_sr] using heq
    · exact (hne rfl).elim
  apply Fin.ext
  have hval := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
    Nat.mod_eq_of_lt j.isLt] using hval

/-- Both alternating words of length at most n are canonical reduced words. -/
theorem alternatingWord_isReduced (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (hne : first ≠ second) (size : ℕ) (hsize : size ≤ n) :
    IsReduced n hthree (CoxeterSystem.alternatingWord first second size) := by
  have hbound : size < 2 * n := by omega
  by_cases heven : Even size
  · have hnodup := initial_inversion_sequence_nodup n hthree first second
      (odd_products_injective n hthree first second hne) size hsize
    rw [← CoxeterSystem.leftInvSeq_take,
      CoxeterSystem.listTake_alternatingWord first second n size hbound,
      ite_eq_left heven] at hnodup
    exact isReduced_of_nodup_leftInvSeq n hthree _ hnodup
  · have hnodup := initial_inversion_sequence_nodup n hthree second first
      (odd_products_injective n hthree second first hne.symm) size hsize
    rw [← CoxeterSystem.leftInvSeq_take,
      CoxeterSystem.listTake_alternatingWord second first n size hbound,
      ite_eq_right heven] at hnodup
    exact isReduced_of_nodup_leftInvSeq n hthree _ hnodup

/-- A bounded alternating word has canonical length equal to its word length. -/
theorem length_alternatingWord (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (hne : first ≠ second) (size : ℕ) (hsize : size ≤ n) :
    length n hthree ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second size)) = size := by
  change (coxeterSystem n hthree).length ((coxeterSystem n hthree).wordProd
    (CoxeterSystem.alternatingWord first second size)) = size
  rw [(alternatingWord_isReduced n hthree first second hne size hsize).eq,
    CoxeterSystem.length_alternatingWord]

/-- The product of an even alternating word is a power of a simple-generator product. -/
theorem alternatingWord_even_wordProd (n : ℕ) (hthree : 3 ≤ n)
    (first second : Fin 2) (halfLength : ℕ) :
    (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second (2 * halfLength)) =
      (simpleReflection n first * simpleReflection n second) ^ halfLength := by
  rw [CoxeterSystem.prod_alternatingWord_eq_mul_pow]
  have heven : Even (2 * halfLength) := ⟨halfLength, by omega⟩
  simp only [ite_eq_left heven, one_mul, coxeterSystem_simple]
  have hhalf : (2 * halfLength) / 2 = halfLength := by omega
  rw [hhalf]

/-- A rotation in the first half of the polygon has canonical length twice its exponent. -/
theorem length_r_of_twice_le (n : ℕ) (hthree : 3 ≤ n) (exponent : ℕ)
    (hbound : 2 * exponent ≤ n) :
    length n hthree (DihedralGroup.r (exponent : ZMod n)) = 2 * exponent := by
  have hprod := alternatingWord_even_wordProd n hthree 0 1 exponent
  simp only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, sub_zero,
    DihedralGroup.r_pow, one_mul] at hprod
  rw [← hprod]
  exact length_alternatingWord n hthree 0 1 (by decide) _ hbound

/-- The inverse rotation has the same canonical length in the first half of the polygon. -/
theorem length_r_neg_of_twice_le (n : ℕ) (hthree : 3 ≤ n) (exponent : ℕ)
    (hbound : 2 * exponent ≤ n) :
    length n hthree (DihedralGroup.r (-(exponent : ZMod n))) = 2 * exponent := by
  rw [← DihedralGroup.inv_r, length_inv]
  exact length_r_of_twice_le n hthree exponent hbound

/-- The reflection of root index i has canonical length 2 floor(i/2)+1. -/
theorem length_rootReflection (n : ℕ) (hthree : 3 ≤ n) (index : PositiveRootIndex n) :
    length n hthree (rootReflection index) = 2 * (index.val / 2) + 1 := by
  have hbound : 2 * (index.val / 2) + 1 ≤ n := by
    have := index.isLt
    omega
  by_cases heven : index.val % 2 = 0
  · rw [rootReflection_of_even_index index heven]
    unfold rotation
    have hprod := alternatingWord_odd_wordProd n hthree 0 1 (index.val / 2)
    simp only [simpleReflection_zero, simpleReflection_one] at hprod
    rw [← hprod]
    exact length_alternatingWord n hthree 1 0 (by decide) _ hbound
  · rw [rootReflection_of_odd_index index heven]
    have hprod := alternatingWord_odd_wordProd n hthree 1 0 (index.val / 2)
    simp only [simpleReflection_zero, simpleReflection_one] at hprod
    rw [← hprod]
    exact length_alternatingWord n hthree 0 1 (by decide) _ hbound

/-- Rotation length is twice the shorter distance of its exponent from zero. -/
theorem length_r (n : ℕ) (hthree : 3 ≤ n) (coordinate : ZMod n) :
    length n hthree (DihedralGroup.r coordinate) =
      2 * min coordinate.val (n - coordinate.val) := by
  let : NeZero n := ⟨by omega⟩
  have hlt := coordinate.val_lt
  by_cases hhalf : coordinate.val ≤ n - coordinate.val
  · rw [min_eq_left hhalf]
    simpa only [ZMod.natCast_zmod_val] using
      length_r_of_twice_le n hthree coordinate.val (by omega)
  · rw [min_eq_right (by omega : n - coordinate.val ≤ coordinate.val)]
    have hcast : ((n - coordinate.val : ℕ) : ZMod n) = -coordinate := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
    have hlength := length_r_neg_of_twice_le n hthree (n - coordinate.val) (by omega)
    rwa [hcast, neg_neg] at hlength

/-- A reflection in the first alternating chain has its odd expression length. -/
theorem length_sr_neg_of_twice_add_one_le (n : ℕ) (hthree : 3 ≤ n) (exponent : ℕ)
    (hbound : 2 * exponent + 1 ≤ n) :
    length n hthree (DihedralGroup.sr (-(exponent : ZMod n))) = 2 * exponent + 1 := by
  have hprod := alternatingWord_odd_wordProd n hthree 0 1 exponent
  simp only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, sub_zero,
    DihedralGroup.r_pow, one_mul, DihedralGroup.r_mul_sr, zero_sub] at hprod
  rw [← hprod]
  exact length_alternatingWord n hthree 1 0 (by decide) _ hbound

/-- A reflection in the second alternating chain has its odd expression length. -/
theorem length_sr_add_one_of_twice_add_one_le (n : ℕ) (hthree : 3 ≤ n) (exponent : ℕ)
    (hbound : 2 * exponent + 1 ≤ n) :
    length n hthree (DihedralGroup.sr ((exponent : ZMod n) + 1)) =
      2 * exponent + 1 := by
  have hprod := alternatingWord_odd_wordProd n hthree 1 0 exponent
  simp [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
    secondSimpleReflection, DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
    DihedralGroup.r_mul_sr, add_comm] at hprod
  rw [← hprod]
  simpa only [Nat.add_comm] using
    length_alternatingWord n hthree 0 1 (by decide) _ hbound

/-- Reflection length is the shorter odd distance in its two alternating expressions. -/
theorem length_sr (n : ℕ) (hthree : 3 ≤ n) (coordinate : ZMod n) :
    length n hthree (DihedralGroup.sr coordinate) =
      if coordinate = 0 then 1 else
        min (2 * coordinate.val - 1) (2 * (n - coordinate.val) + 1) := by
  let : NeZero n := ⟨by omega⟩
  by_cases hzero : coordinate = 0
  · rw [ite_eq_left hzero, hzero]
    simpa only [simpleReflection_zero, firstSimpleReflection] using
      length_simpleReflection n hthree 0
  · rw [ite_eq_right hzero]
    have hlt := coordinate.val_lt
    have hpos : 0 < coordinate.val := by
      by_contra h
      have hval : coordinate.val = 0 := by omega
      apply hzero
      rw [← ZMod.natCast_zmod_val coordinate, hval, Nat.cast_zero]
    by_cases hfirst : 2 * coordinate.val - 1 ≤ n
    · rw [min_eq_left (by omega)]
      have hcast : ((coordinate.val - 1 : ℕ) : ZMod n) + 1 = coordinate := by
        rw [Nat.cast_sub (by omega), Nat.cast_one, sub_add_cancel,
          ZMod.natCast_zmod_val]
      have hlength := length_sr_add_one_of_twice_add_one_le n hthree
        (coordinate.val - 1) (by omega)
      rw [hcast] at hlength
      convert hlength using 1
      omega
    · rw [min_eq_right (by omega)]
      have hcast : ((n - coordinate.val : ℕ) : ZMod n) = -coordinate := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
      have hlength := length_sr_neg_of_twice_add_one_le n hthree
        (n - coordinate.val) (by omega)
      rwa [hcast, neg_neg] at hlength

end Schubert.Dihedral
