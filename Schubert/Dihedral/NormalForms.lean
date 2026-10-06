import Schubert.Dihedral.AlternatingWords

/-! # Alternating normal forms of dihedral elements

Every element has an alternating expression of length at most n. Since these
expressions are reduced, their length equals canonical Coxeter length.
-/

namespace Schubert.Dihedral

/-- Every dihedral element has a bounded alternating expression. -/
theorem exists_bounded_alternatingWord (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    ∃ first second : Fin 2, ∃ size : ℕ, first ≠ second ∧ size ≤ n ∧
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second size) = element := by
  let : NeZero n := ⟨by omega⟩
  cases element with
  | r coordinate =>
    have hlt := coordinate.val_lt
    by_cases hhalf : 2 * coordinate.val ≤ n
    · refine ⟨0, 1, 2 * coordinate.val, by decide, hhalf, ?_⟩
      have hprod := alternatingWord_even_wordProd n hthree 0 1 coordinate.val
      simpa only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, sub_zero,
        DihedralGroup.r_pow, one_mul, ZMod.natCast_zmod_val] using hprod
    · refine ⟨1, 0, 2 * (n - coordinate.val), by decide, by omega, ?_⟩
      have hcast : ((n - coordinate.val : ℕ) : ZMod n) = -coordinate := by
        rw [Nat.cast_sub (by omega), ZMod.natCast_self, ZMod.natCast_zmod_val, zero_sub]
      have hprod := alternatingWord_even_wordProd n hthree 1 0 (n - coordinate.val)
      simpa only [simpleReflection_zero, simpleReflection_one, firstSimpleReflection,
        secondSimpleReflection, DihedralGroup.sr_mul_sr, zero_sub,
        DihedralGroup.r_pow, neg_mul, one_mul, hcast, neg_neg] using hprod
  | sr coordinate =>
    obtain ⟨index, hindex⟩ := exists_rootReflection_eq_sr n hthree coordinate
    have hbound : 2 * (index.val / 2) + 1 ≤ n := by
      have := index.isLt
      omega
    by_cases heven : index.val % 2 = 0
    · refine ⟨1, 0, 2 * (index.val / 2) + 1, by decide, hbound, ?_⟩
      rw [rootReflection_of_even_index index heven, rotation] at hindex
      have hprod := alternatingWord_odd_wordProd n hthree 0 1 (index.val / 2)
      simp only [simpleReflection_zero, simpleReflection_one] at hprod
      exact hprod.trans hindex
    · refine ⟨0, 1, 2 * (index.val / 2) + 1, by decide, hbound, ?_⟩
      rw [rootReflection_of_odd_index index heven] at hindex
      have hprod := alternatingWord_odd_wordProd n hthree 1 0 (index.val / 2)
      simp only [simpleReflection_zero, simpleReflection_one] at hprod
      exact hprod.trans hindex

/-- Every element is represented by an alternating word of its canonical length. -/
theorem exists_alternatingWord_length (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    ∃ first second : Fin 2, first ≠ second ∧
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second (length n hthree element)) = element := by
  obtain ⟨first, second, size, hne, hbound, hprod⟩ :=
    exists_bounded_alternatingWord n hthree element
  have hlength := length_alternatingWord n hthree first second hne size hbound
  rw [hprod] at hlength
  exact ⟨first, second, hne, by simpa only [hlength] using hprod⟩

end Schubert.Dihedral
