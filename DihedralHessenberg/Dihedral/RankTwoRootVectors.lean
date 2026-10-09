import DihedralHessenberg.Dihedral.RootVectorAscent
import DihedralHessenberg.Dihedral.RankTwoEndpoints

/-! # Simple-vector rank-two descent, ascent and inversion facts -/

namespace Schubert.Dihedral

/-- The unique element of maximal canonical length. -/
noncomputable def longestElement (n : ℕ) (hthree : 3 ≤ n) : DihedralGroup n :=
  (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)

/-- Maximal canonical length characterizes the named longest element. -/
theorem length_eq_longest (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    length n hthree element = n ↔ element = longestElement n hthree :=
  length_eq_n_iff_eq_alternatingWord n hthree element

private theorem exists_simple {n : ℕ} {hthree : 3 ≤ n} {alpha : PositiveRoot n}
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
  rcases hsimple with hfirst | hsecond
  · exact ⟨0, hfirst⟩
  · exact ⟨1, hsecond⟩

/-- A nonendpoint element has a unique simple-vector left descent. -/
theorem unique_root_descent (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (hneOne : element ≠ 1) (hneTop : element ≠ longestElement n hthree) :
    ∃! alpha : PositiveRoot n,
      (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) ∧
        length n hthree (alpha.reflection * element) = length n hthree element - 1 := by
  obtain ⟨simple, hlength, hunique⟩ :=
    _root_.Schubert.Dihedral.SimpleDescents.unique_of_ne_endpoints n hthree element hneOne hneTop
  have hsimple : simpleRoot n hthree simple = simpleRoot n hthree 0 ∨
      simpleRoot n hthree simple = simpleRoot n hthree 1 := by
    fin_cases simple
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨simpleRoot n hthree simple, ⟨hsimple, ?_⟩, ?_⟩
  · rw [simpleRoot_reflection]
    exact hlength
  · intro alpha halpha
    obtain ⟨other, rfl⟩ := exists_simple halpha.1
    have hother := hunique other (by simpa only [simpleRoot_reflection] using halpha.2)
    rw [hother]

/-- A nonendpoint element has a unique simple-vector left ascent. -/
theorem unique_root_ascent (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n)
    (hneOne : element ≠ 1) (hneTop : element ≠ longestElement n hthree) :
    ∃! alpha : PositiveRoot n,
      (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) ∧
        length n hthree (alpha.reflection * element) = length n hthree element + 1 := by
  obtain ⟨simple, hlength, hunique⟩ :=
    _root_.Schubert.Dihedral.SimpleAscents.unique_of_ne_endpoints n hthree element hneOne hneTop
  have hsimple : simpleRoot n hthree simple = simpleRoot n hthree 0 ∨
      simpleRoot n hthree simple = simpleRoot n hthree 1 := by
    fin_cases simple
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨simpleRoot n hthree simple, ⟨hsimple, ?_⟩, ?_⟩
  · rw [simpleRoot_reflection]
    exact hlength
  · intro alpha halpha
    obtain ⟨other, rfl⟩ := exists_simple halpha.1
    have hother := hunique other (by simpa only [simpleRoot_reflection] using halpha.2)
    rw [hother]

namespace PositiveRoot

/-- A simple-vector ascent inserts its positive inverse image into right inversions. -/
theorem right_ascent {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    realAction n element⁻¹ alpha.val ∈ positiveRoots n ∧
      rightInversionSet n (alpha.reflection * element) =
        insert (realAction n element⁻¹ alpha.val) (rightInversionSet n element) ∧
      realAction n element⁻¹ alpha.val ∉ rightInversionSet n element := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hascent ⊢
  exact rightInversionSet_ascent n hthree simple element hascent

/-- A simple-vector ascent inserts its vector and acts on old left inversions. -/
theorem left_ascent {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    leftInversionSet n (alpha.reflection * element) =
      insert alpha.val (realAction n alpha.reflection '' leftInversionSet n element) := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hascent ⊢
  exact leftInversionSet_ascent n hthree simple element hascent

/-- The simple vector is disjoint from its images of old left inversion vectors. -/
theorem left_ascent_disjoint {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    alpha.val ∉ realAction n alpha.reflection '' leftInversionSet n element := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hascent ⊢
  exact leftInversionSet_ascent_disjoint n hthree simple element hascent

end PositiveRoot

end Schubert.Dihedral
