import Schubert.Dihedral.NormalForms

/-! # Rank-two Bruhat comparison

Every longer alternating word contains both shorter alternating words as subwords.
Hence distinct dihedral elements are Bruhat comparable exactly in increasing length.
-/

namespace Schubert.Dihedral

private theorem shorter_alternatingWords_sublist {B : Type*} (first second : B)
    (short long : ℕ) (hshort : short < long) :
    (CoxeterSystem.alternatingWord first second short).Sublist
        (CoxeterSystem.alternatingWord first second long) ∧
      (CoxeterSystem.alternatingWord second first short).Sublist
        (CoxeterSystem.alternatingWord first second long) := by
  induction long generalizing first second short with
  | zero => omega
  | succ long ih =>
    by_cases hlt : short < long
    · obtain ⟨hsame, hswap⟩ := ih second first short hlt
      have hprefix : (CoxeterSystem.alternatingWord second first long).Sublist
          (CoxeterSystem.alternatingWord first second (long + 1)) := by
        rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append]
        exact List.sublist_append_left _ _
      exact ⟨hswap.trans hprefix, hsame.trans hprefix⟩
    · have heq : short = long := by omega
      subst short
      constructor
      · rw [CoxeterSystem.alternatingWord_succ']
        exact List.sublist_cons_self _ _
      · rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append]
        exact List.sublist_append_left _ _

private theorem distinct_pairs_eq_or_swap (first second third fourth : Fin 2)
    (hfirst : first ≠ second) (hsecond : third ≠ fourth) :
    (first = third ∧ second = fourth) ∨ (first = fourth ∧ second = third) := by
  fin_cases first <;> fin_cases second <;> fin_cases third <;> fin_cases fourth <;> simp_all

/-- Any shorter alternating word occurs inside either longer alternating word. -/
theorem alternatingWord_sublist_of_length_lt (first second third fourth : Fin 2)
    (hfirst : first ≠ second) (hsecond : third ≠ fourth)
    (short long : ℕ) (hshort : short < long) :
    (CoxeterSystem.alternatingWord first second short).Sublist
      (CoxeterSystem.alternatingWord third fourth long) := by
  obtain (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) :=
    distinct_pairs_eq_or_swap first second third fourth hfirst hsecond
  · exact (shorter_alternatingWords_sublist _ _ short long hshort).1
  · exact (shorter_alternatingWords_sublist _ _ short long hshort).2

/-- Strictly smaller canonical length implies Bruhat comparison in rank two. -/
theorem bruhatLE_of_length_lt (n : ℕ) (hthree : 3 ≤ n) {u v : DihedralGroup n}
    (hlength : length n hthree u < length n hthree v) : BruhatLE n hthree u v := by
  obtain ⟨first, second, hfirst, hu⟩ := exists_alternatingWord_length n hthree u
  obtain ⟨third, fourth, hsecond, hv⟩ := exists_alternatingWord_length n hthree v
  rw [← hv]
  apply (bruhatLE_iff_exists_sublist n hthree u
    (alternatingWord_isReduced n hthree third fourth hsecond _
      (length_le_polygon_parameter n hthree v))).mpr
  exact ⟨CoxeterSystem.alternatingWord first second (length n hthree u),
    alternatingWord_sublist_of_length_lt first second third fourth hfirst hsecond _ _ hlength,
    hu⟩

/-- Dihedral Bruhat comparison is equality or a strict increase in canonical length. -/
theorem bruhatLE_iff_eq_or_length_lt (n : ℕ) (hthree : 3 ≤ n) (u v : DihedralGroup n) :
    BruhatLE n hthree u v ↔ u = v ∨ length n hthree u < length n hthree v := by
  constructor
  · intro hle
    by_cases heq : u = v
    · exact Or.inl heq
    · exact Or.inr (CoxeterSystem.BruhatLE.length_lt_of_ne hle heq)
  · rintro (rfl | hlength)
    · exact bruhatLE_refl n hthree _
    · exact bruhatLE_of_length_lt n hthree hlength

end Schubert.Dihedral
