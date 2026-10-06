import Schubert.Dihedral.RankTwoEndpoints

/-! # Recognizing the unique element with a given simple ascent in each length layer -/

namespace Schubert.Dihedral

private theorem simple_eq_next_of_alternating_left_ascent (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : length n hthree (simpleReflection n simple * element) =
      length n hthree element + 1) (hpositive : 0 < length n hthree element)
    (first second : Fin 2) (hne : first ≠ second)
    (hprod : (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second (length n hthree element)) = element) :
    simple = if Even (length n hthree element) then second else first := by
  have hshort : length n hthree element < n := by
    have hbound := length_le_polygon_parameter n hthree (simpleReflection n simple * element)
    omega
  let next := if Even (length n hthree element) then second else first
  have hnextWord : (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord first second (length n hthree element + 1)) =
        simpleReflection n next * element := by
    rw [CoxeterSystem.alternatingWord_succ', CoxeterSystem.wordProd_cons,
      coxeterSystem_simple, hprod]
  have hnextLength : length n hthree (simpleReflection n next * element) =
      length n hthree element + 1 := by
    rw [← hnextWord, length_alternatingWord n hthree first second hne _ (by omega)]
  obtain ⟨ascent, _, hunique⟩ :=
    existsUnique_simple_left_ascent n hthree element hpositive hshort
  exact (hunique simple hascent).trans (hunique next hnextLength).symm

/-- In a fixed length layer, a prescribed simple reflection ascends at only one element. -/
theorem _root_.Schubert.Dihedral.SimpleAscents.eq_of_length_eq (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (firstElement secondElement : DihedralGroup n)
    (hlength : length n hthree firstElement = length n hthree secondElement)
    (hfirst : length n hthree (simpleReflection n simple * firstElement) =
      length n hthree firstElement + 1)
    (hsecond : length n hthree (simpleReflection n simple * secondElement) =
      length n hthree secondElement + 1) : firstElement = secondElement := by
  by_cases hzero : length n hthree firstElement = 0
  · have hfirstOne : firstElement = 1 := (coxeterSystem n hthree).length_eq_zero_iff.mp hzero
    have hsecondZero : length n hthree secondElement = 0 := hlength.symm.trans hzero
    have hsecondOne : secondElement = 1 :=
      (coxeterSystem n hthree).length_eq_zero_iff.mp hsecondZero
    exact hfirstOne.trans hsecondOne.symm
  · obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree firstElement
    obtain ⟨otherFirst, otherSecond, hotherNe, hotherProd⟩ :=
      exists_alternatingWord_length n hthree secondElement
    have hchoice := simple_eq_next_of_alternating_left_ascent n hthree simple firstElement
      hfirst (by omega) first second hne hprod
    have hotherChoice := simple_eq_next_of_alternating_left_ascent n hthree simple secondElement
      hsecond (by omega) otherFirst otherSecond hotherNe hotherProd
    rw [← hlength] at hotherChoice hotherProd
    have hchoices := hchoice.symm.trans hotherChoice
    by_cases heven : Even (length n hthree firstElement)
    · simp only [ite_eq_left heven] at hchoices
      fin_cases first <;> fin_cases second <;> fin_cases otherFirst <;> fin_cases otherSecond
      all_goals first
        | exact (hne rfl).elim
        | exact (hotherNe rfl).elim
        | exact hprod.symm.trans hotherProd
        | norm_num at hchoices
    · simp only [ite_eq_right heven] at hchoices
      fin_cases first <;> fin_cases second <;> fin_cases otherFirst <;> fin_cases otherSecond
      all_goals first
        | exact (hne rfl).elim
        | exact (hotherNe rfl).elim
        | exact hprod.symm.trans hotherProd
        | norm_num at hchoices

/-- In a fixed length layer, a prescribed simple reflection descends at only one element. -/
theorem _root_.Schubert.Dihedral.SimpleDescents.eq_of_length_eq (n : ℕ) (hthree : 3 ≤ n)
    (simple : Fin 2) (firstElement secondElement : DihedralGroup n)
    (hlength : length n hthree firstElement = length n hthree secondElement)
    (hfirst : length n hthree (simpleReflection n simple * firstElement) + 1 =
      length n hthree firstElement)
    (hsecond : length n hthree (simpleReflection n simple * secondElement) + 1 =
      length n hthree secondElement) : firstElement = secondElement := by
  have heq := _root_.Schubert.Dihedral.SimpleAscents.eq_of_length_eq n hthree simple
    (simpleReflection n simple * firstElement) (simpleReflection n simple * secondElement)
    (by omega) (by rw [← mul_assoc, simpleReflection_mul_self, one_mul, hfirst])
      (by rw [← mul_assoc, simpleReflection_mul_self, one_mul, hsecond])
  exact mul_left_cancel heq

end Schubert.Dihedral
