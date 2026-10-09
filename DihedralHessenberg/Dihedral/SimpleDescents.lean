import DihedralHessenberg.Dihedral.NormalForms

/-! # Simple descents and ascents in rank two

Every element of length strictly between zero and n has one simple left descent
and one simple left ascent.
-/

namespace Schubert.Dihedral

/-- An intermediate-length element has distinct simple descent and ascent generators. -/
theorem exists_simple_left_descent_ascent (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (hpositive : 0 < length n hthree element)
    (hshort : length n hthree element < n) :
    ∃ descent ascent : Fin 2, descent ≠ ascent ∧
      length n hthree (simpleReflection n descent * element) + 1 = length n hthree element ∧
      length n hthree (simpleReflection n ascent * element) = length n hthree element + 1 := by
  obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element
  let size := length n hthree element
  have hsub : size - 1 + 1 = size := by omega
  let descent := if Even (size - 1) then second else first
  let ascent := if Even size then second else first
  have hdistinct : descent ≠ ascent := by
    dsimp only [descent, ascent]
    have hparity : Even (size - 1 + 1) ↔ ¬Even (size - 1) := Nat.even_add_one
    rw [hsub] at hparity
    by_cases heven : Even (size - 1)
    · rw [ite_eq_left heven, ite_eq_right (by tauto)]
      exact hne.symm
    · rw [ite_eq_right heven, ite_eq_left (by tauto)]
      exact hne
  have hprevious : element = simpleReflection n descent *
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord first second (size - 1)) := by
    calc
      element = (coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord first second size) := hprod.symm
      _ = (coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord first second (size - 1 + 1)) := by rw [hsub]
      _ = _ := by rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons,
        coxeterSystem_simple]
  have hnext : (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second (size + 1)) =
      simpleReflection n ascent * element := by
    rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons,
      coxeterSystem_simple, hprod]
  refine ⟨descent, ascent, hdistinct, ?_, ?_⟩
  · have hcancel : simpleReflection n descent * element =
        (coxeterSystem n hthree).wordProd
          (CoxeterSystem.alternatingWord first second (size - 1)) := by
      rw [hprevious, ← mul_assoc, simpleReflection_mul_self, one_mul]
    rw [hcancel, length_alternatingWord n hthree first second hne _ (by omega)]
    exact hsub
  · rw [← hnext, length_alternatingWord n hthree first second hne _ (by omega)]

private theorem eq_descent_or_ascent (descent ascent index : Fin 2)
    (hne : descent ≠ ascent) : index = descent ∨ index = ascent := by
  fin_cases descent <;> fin_cases ascent <;> fin_cases index <;> simp_all

/-- An intermediate-length element has a unique simple left descent. -/
theorem existsUnique_simple_left_descent (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (hpositive : 0 < length n hthree element)
    (hshort : length n hthree element < n) :
    ∃! generator : Fin 2,
      length n hthree (simpleReflection n generator * element) + 1 =
        length n hthree element := by
  obtain ⟨descent, ascent, hne, hdown, hup⟩ :=
    exists_simple_left_descent_ascent n hthree element hpositive hshort
  refine ⟨descent, hdown, ?_⟩
  intro index hindex
  obtain (rfl | rfl) := eq_descent_or_ascent descent ascent index hne
  · rfl
  · omega

/-- An intermediate-length element has a unique simple left ascent. -/
theorem existsUnique_simple_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (hpositive : 0 < length n hthree element)
    (hshort : length n hthree element < n) :
    ∃! generator : Fin 2,
      length n hthree (simpleReflection n generator * element) =
        length n hthree element + 1 := by
  obtain ⟨descent, ascent, hne, hdown, hup⟩ :=
    exists_simple_left_descent_ascent n hthree element hpositive hshort
  refine ⟨ascent, hup, ?_⟩
  intro index hindex
  obtain (rfl | rfl) := eq_descent_or_ascent descent ascent index hne
  · omega
  · rfl

end Schubert.Dihedral
