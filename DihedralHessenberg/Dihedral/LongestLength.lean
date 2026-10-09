import DihedralHessenberg.Dihedral.LongestElement

/-! # Length reversal by the longest element

An alternating reduced expression for the longest element can begin with a
reduced expression for any element. Its remaining suffix has complementary length.
-/

namespace Schubert.Dihedral

private theorem exists_reduced_prefix_top (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    ∃ word : List (Fin 2), IsReduced n hthree word ∧ word.length = n ∧
      (coxeterSystem n hthree).wordProd word =
        (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) ∧
      (coxeterSystem n hthree).wordProd (word.take (length n hthree element)) = element := by
  obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element
  have hlength := length_le_polygon_parameter n hthree element
  have hbound : length n hthree element < 2 * n := by omega
  obtain ⟨third, fourth, hdistinct, htake⟩ :
      ∃ third fourth : Fin 2, third ≠ fourth ∧
        (CoxeterSystem.alternatingWord third fourth (2 * n)).take
            (length n hthree element) =
          CoxeterSystem.alternatingWord first second (length n hthree element) := by
    by_cases heven : Even (length n hthree element)
    · refine ⟨first, second, hne, ?_⟩
      rw [CoxeterSystem.listTake_alternatingWord _ _ n _ hbound, ite_eq_left heven]
    · refine ⟨second, first, hne.symm, ?_⟩
      rw [CoxeterSystem.listTake_alternatingWord _ _ n _ hbound, ite_eq_right heven]
  let word := (CoxeterSystem.alternatingWord third fourth (2 * n)).take n
  have hwordLength : word.length = n := by
    simp only [word, List.length_take, CoxeterSystem.length_alternatingWord]
    omega
  have hwordReduced : IsReduced n hthree word := by
    dsimp only [word]
    rw [CoxeterSystem.listTake_alternatingWord third fourth n n (by omega)]
    split_ifs
    · exact alternatingWord_isReduced n hthree third fourth hdistinct n le_rfl
    · exact alternatingWord_isReduced n hthree fourth third hdistinct.symm n le_rfl
  refine ⟨word, hwordReduced, hwordLength, ?_, ?_⟩
  · apply (length_eq_n_iff_eq_alternatingWord n hthree _).mp
    exact hwordReduced.eq.trans hwordLength
  · dsimp only [word]
    rw [List.take_take, min_eq_left hlength, htake, hprod]

/-- The longest alternating product is its own inverse. -/
theorem alternatingWord_top_inv (n : ℕ) (hthree : 3 ≤ n) :
    ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n))⁻¹ =
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) := by
  apply (length_eq_n_iff_eq_alternatingWord n hthree _).mp
  rw [length_inv, length_alternatingWord n hthree 0 1 (by decide) n le_rfl]

/-- Removing any element from the left of the longest element gives complementary length. -/
theorem length_inv_mul_alternatingWord_top (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    length n hthree (element⁻¹ * (coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n)) = n - length n hthree element := by
  obtain ⟨word, hword, hwordLength, htop, hprefix⟩ :=
    exists_reduced_prefix_top n hthree element
  have hsplit : (coxeterSystem n hthree).wordProd word = element *
      (coxeterSystem n hthree).wordProd (word.drop (length n hthree element)) := by
    calc
      _ = (coxeterSystem n hthree).wordProd
          (word.take (length n hthree element) ++ word.drop (length n hthree element)) := by
        rw [List.take_append_drop]
      _ = _ := by rw [CoxeterSystem.wordProd_append, hprefix]
  rw [← htop, hsplit, inv_mul_cancel_left]
  exact (hword.drop (length n hthree element)).eq.trans
    (by rw [List.length_drop, hwordLength])

/-- Left multiplication by the longest element reverses canonical length. -/
theorem length_alternatingWord_top_mul (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    length n hthree ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n) * element) = n - length n hthree element := by
  rw [← length_inv n hthree (_ * element), mul_inv_rev, alternatingWord_top_inv]
  exact length_inv_mul_alternatingWord_top n hthree element

end Schubert.Dihedral
