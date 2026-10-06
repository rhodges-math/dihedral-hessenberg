import Schubert.Dihedral.RankTwoBruhat

/-! # The unique longest dihedral element

The two alternating expressions of length n coincide. Their common product is
the unique element of length n, and both of its indexed inversion sets are full.
-/

namespace Schubert.Dihedral

/-- The two orientations of the alternating expression of length n have equal products. -/
theorem alternatingWord_top_wordProd_eq (n : ℕ) (hthree : 3 ≤ n) :
    (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) =
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 1 0 n) := by
  have hbraid := (coxeterSystem n hthree).wordProd_braidWord_eq 0 1
  simpa only [CoxeterSystem.braidWord,
    coxeterMatrix_apply_of_ne n hthree (by decide : (0 : Fin 2) ≠ 1),
    coxeterMatrix_apply_of_ne n hthree (by decide : (1 : Fin 2) ≠ 0)] using hbraid

/-- Length n characterizes the common longest alternating product. -/
theorem length_eq_n_iff_eq_alternatingWord (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    length n hthree element = n ↔ element =
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) := by
  constructor
  · intro hlength
    obtain ⟨first, second, hne, hprod⟩ := exists_alternatingWord_length n hthree element
    rw [hlength] at hprod
    fin_cases first <;> fin_cases second
    · exact (hne rfl).elim
    · exact hprod.symm
    · exact hprod.symm.trans (alternatingWord_top_wordProd_eq n hthree).symm
    · exact (hne rfl).elim
  · rintro rfl
    exact length_alternatingWord n hthree 0 1 (by decide) n le_rfl

/-- Every dihedral element lies below the longest alternating product in Bruhat order. -/
theorem bruhatLE_alternatingWord_top (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    BruhatLE n hthree element
      ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)) := by
  rw [bruhatLE_iff_eq_or_length_lt]
  by_cases htop : length n hthree element = n
  · exact Or.inl ((length_eq_n_iff_eq_alternatingWord n hthree element).mp htop)
  · right
    rw [length_alternatingWord n hthree 0 1 (by decide) n le_rfl]
    have := length_le_polygon_parameter n hthree element
    omega

/-- All positive roots are left inversions of the longest element. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.left_top (n : ℕ) (hthree : 3 ≤ n) :
    leftInversions n hthree
      ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [card_leftInversions, length_alternatingWord n hthree 0 1 (by decide) n le_rfl,
    Fintype.card_fin]

/-- All positive roots are right inversions of the longest element. -/
theorem _root_.Schubert.Dihedral.IndexedInversions.right_top (n : ℕ) (hthree : 3 ≤ n) :
    rightInversions n hthree
      ((coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)) = Finset.univ := by
  classical
  apply Finset.eq_univ_of_card
  rw [card_rightInversions, length_alternatingWord n hthree 0 1 (by decide) n le_rfl,
    Fintype.card_fin]

end Schubert.Dihedral
