import Schubert.DihedralSplines.HessenbergDegree
import Schubert.Dihedral.LongestLength

/-! # Complementary Hessenberg inversions

Left multiplication by the longest element complements the right inversion set.
It therefore complements the H-inversion set inside H and reverses H-length.
-/

namespace Schubert.Dihedral

/-- Left multiplication by the longest element complements right inversions. -/
theorem rightInversions_alternatingWord_top_mul (n : ℕ) (hthree : 3 ≤ n)
    (element : DihedralGroup n) :
    rightInversions n hthree ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n) * element) =
      (rightInversions n hthree element)ᶜ := by
  classical
  ext index
  rw [mem_rightInversions, Finset.mem_compl, mem_rightInversions, mul_assoc,
    length_alternatingWord_top_mul, length_alternatingWord_top_mul]
  have hfirst := length_le_polygon_parameter n hthree element
  have hsecond := length_le_polygon_parameter n hthree (element * rootReflection index)
  have hne : length n hthree (element * rootReflection index) ≠ length n hthree element :=
    (rootReflection_isReflection n hthree index).length_mul_left_ne element
  omega

end Schubert.Dihedral

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The longest element complements H-inversions inside the root set H. -/
theorem inversions_alternatingWord_top_mul (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ideal.inversions ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n) * element) =
      ideal.roots \ ideal.inversions element := by
  classical
  rw [inversions, rightInversions_alternatingWord_top_mul]
  ext index
  simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, inversions]
  tauto

/-- The H-lengths of longest-related vertices sum to the number of roots of H. -/
theorem length_alternatingWord_top_mul_add (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ideal.length ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n) * element) + ideal.length element =
      ideal.roots.card := by
  rw [length, ideal.inversions_alternatingWord_top_mul]
  exact Finset.card_sdiff_add_card_eq_card (ideal.inversions_subset_roots element)

end Schubert.DihedralSplines.HessenbergSpace
