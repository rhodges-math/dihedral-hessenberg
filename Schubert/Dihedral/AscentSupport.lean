import Schubert.Dihedral.SimpleRootObjects
import Schubert.Dihedral.RankTwoBruhat
import Schubert.Dihedral.RootSubsetCard

/-! # Simple-root support transfer -/

namespace Schubert.Dihedral

/-- Every geometric left-inversion set is finite. -/
theorem finite_leftInversionSet (n : ℕ) (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (leftInversionSet n element).Finite := by
  rw [← image_leftInversions n hthree element]
  exact (leftInversions n hthree element).finite_toSet.image (positiveRoot n)

/-- The identity lies below every vertex in canonical Bruhat order. -/
theorem one_bruhatLE (n : ℕ) (hthree : 3 ≤ n) (vertex : DihedralGroup n) :
    BruhatLE n hthree 1 vertex := by
  by_cases heq : vertex = 1
  · subst vertex
    exact bruhatLE_refl n hthree 1
  apply bruhatLE_of_length_lt n hthree
  rw [length_one]
  have hne : length n hthree vertex ≠ 0 := by
    intro hzero
    exact heq ((coxeterSystem n hthree).length_eq_zero_iff.mp hzero)
  omega

/-- A simple-vector left ascent preserves exclusion from an upper support. -/
theorem ascent_support {n : ℕ} {hthree : 3 ≤ n} (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element vertex : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1)
    (hnot : ¬ BruhatLE n hthree element vertex) :
    ¬ BruhatLE n hthree (alpha.reflection * element) vertex ∧
      ¬ BruhatLE n hthree (alpha.reflection * element) (alpha.reflection * vertex) := by
  have hne : element ≠ vertex := by
    intro heq
    subst vertex
    exact hnot (bruhatLE_refl n hthree element)
  have hbound : length n hthree vertex ≤ length n hthree element := by
    by_contra hlt
    exact hnot (bruhatLE_of_length_lt n hthree (by omega))
  have hsimpleLength : length n hthree alpha.reflection = 1 := by
    rcases hsimple with rfl | rfl <;>
      rw [simpleRoot_reflection, length_simpleReflection]
  have hproduct := (coxeterSystem n hthree).length_mul_le alpha.reflection vertex
  change length n hthree (alpha.reflection * vertex) ≤
    length n hthree alpha.reflection + length n hthree vertex at hproduct
  rw [hsimpleLength] at hproduct
  constructor
  · intro hle
    have := bruhatLE_length_le n hthree hle
    omega
  · intro hle
    rcases (bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hle with heq | hlt
    · exact hne (mul_left_cancel heq)
    · omega

end Schubert.Dihedral
