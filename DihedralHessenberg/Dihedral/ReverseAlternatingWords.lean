import DihedralHessenberg.Dihedral.AlternatingWords

/-! # Simple descents and ascents of reversed alternating words -/

namespace Schubert.Dihedral

/-- The first generator of a nonempty reversed alternating word is a canonical left descent. -/
theorem _root_.Schubert.Dihedral.Alternating.length_other_mul_reverse (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) (hpositive : 0 < size) (hbound : size ≤ n) :
    length n hthree (simpleReflection n simple.rev * (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse) = size - 1 := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : size ≠ 0)
  rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_concat,
    CoxeterSystem.wordProd_cons, coxeterSystem_simple, ← mul_assoc,
    simpleReflection_mul_self, one_mul]
  have hne : simple.rev ≠ simple := by fin_cases simple <;> decide
  have hword := alternatingWord_isReduced n hthree simple.rev simple hne previous (by omega)
  exact hword.reverse.eq.trans (by simp only [List.length_reverse,
    CoxeterSystem.length_alternatingWord]; omega)

/-- Prepending the other generator to a reversed alternating word below length n is an ascent. -/
theorem _root_.Schubert.Dihedral.Alternating.length_simple_mul_reverse (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (size : ℕ) (hbound : size < n) :
    length n hthree (simpleReflection n simple * (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple simple.rev size).reverse) = size + 1 := by
  have hprod : (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord simple.rev simple (size + 1)).reverse =
        simpleReflection n simple * (coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord simple simple.rev size).reverse := by
    rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.reverse_concat,
      CoxeterSystem.wordProd_cons, coxeterSystem_simple]
  rw [← hprod]
  have hne : simple.rev ≠ simple := by fin_cases simple <;> decide
  have hword := alternatingWord_isReduced n hthree simple.rev simple hne (size + 1) (by omega)
  exact hword.reverse.eq.trans (by simp only [List.length_reverse,
    CoxeterSystem.length_alternatingWord])

end Schubert.Dihedral
