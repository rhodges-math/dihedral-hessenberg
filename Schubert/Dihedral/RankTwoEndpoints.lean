import Schubert.Dihedral.LongestElement
import Schubert.Dihedral.SimpleDescents

/-! # Simple descents and ascents away from the two Bruhat endpoints -/

namespace Schubert.Dihedral

/-- Canonical positive length characterizes nonidentity elements. -/
theorem length_pos_iff_ne_one (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    0 < length n hthree element ↔ element ≠ 1 := by
  change 0 < (coxeterSystem n hthree).length element ↔ element ≠ 1
  rw [Nat.pos_iff_ne_zero, ne_eq, CoxeterSystem.length_eq_zero_iff]

/-- Every nonendpoint element has a unique simple left descent with length one lower. -/
theorem _root_.Schubert.Dihedral.SimpleDescents.unique_of_ne_endpoints (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (hneOne : element ≠ 1)
    (hneTop : element ≠
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)) :
    ∃! simple : Fin 2,
      length n hthree (simpleReflection n simple * element) = length n hthree element - 1 := by
  have hpositive := (length_pos_iff_ne_one n hthree element).mpr hneOne
  have hshort : length n hthree element < n := by
    have hbound := length_le_polygon_parameter n hthree element
    have hnot : length n hthree element ≠ n := by
      exact fun heq => hneTop ((length_eq_n_iff_eq_alternatingWord n hthree element).mp heq)
    omega
  obtain ⟨simple, hsimple, hunique⟩ :=
    existsUnique_simple_left_descent n hthree element hpositive hshort
  refine ⟨simple, by omega, ?_⟩
  intro other hother
  apply hunique other
  omega

/-- Every nonendpoint element has a unique simple left ascent with length one higher. -/
theorem _root_.Schubert.Dihedral.SimpleAscents.unique_of_ne_endpoints (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) (hneOne : element ≠ 1)
    (hneTop : element ≠
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)) :
    ∃! simple : Fin 2,
      length n hthree (simpleReflection n simple * element) = length n hthree element + 1 := by
  have hpositive := (length_pos_iff_ne_one n hthree element).mpr hneOne
  have hshort : length n hthree element < n := by
    have hbound := length_le_polygon_parameter n hthree element
    have hnot : length n hthree element ≠ n := by
      exact fun heq => hneTop ((length_eq_n_iff_eq_alternatingWord n hthree element).mp heq)
    omega
  exact existsUnique_simple_left_ascent n hthree element hpositive hshort

end Schubert.Dihedral
