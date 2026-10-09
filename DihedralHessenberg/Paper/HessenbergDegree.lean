import DihedralHessenberg.Paper.HessenbergInversions
import DihedralHessenberg.Dihedral.LongestElement

/-! # Descending Hessenberg neighbors and the H-degree

H-inversions index exactly the neighbors below a vertex in Bruhat order. Their
distinct endpoints show that H-length is the graph's incoming degree.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- H-inversions are exactly the root-indexed descending Hessenberg edges. -/
theorem mem_inversions_iff_bruhat_descent (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) (index : PositiveRootIndex n) :
    index ∈ ideal.inversions element ↔ index ∈ ideal.roots ∧
      BruhatLE n hthree (element * rootReflection index) element := by
  rw [ideal.mem_inversions, rootReflection_bruhatLE_mul_right_iff]

/-- Root-indexed descending Hessenberg neighbors have distinct endpoints. -/
theorem inversion_neighbor_injective (element : DihedralGroup n) :
    Function.Injective fun index : PositiveRootIndex n => element * rootReflection index := by
  intro first second heq
  exact rootReflection_injective n (mul_left_cancel heq)

/-- A neighbor belongs to the H-inversion image exactly when it is a descending H-edge. -/
theorem mem_image_inversions_iff (ideal : HessenbergSpace n hthree)
    (element neighbor : DihedralGroup n) :
    neighbor ∈ (ideal.inversions element).image (fun index => element * rootReflection index) ↔
      ∃ index ∈ ideal.roots, element * rootReflection index = neighbor ∧
        BruhatLE n hthree neighbor element := by
  classical
  rw [Finset.mem_image]
  constructor
  · rintro ⟨index, hindex, rfl⟩
    obtain ⟨hroot, hdescent⟩ := (ideal.mem_inversions_iff_bruhat_descent element index).mp hindex
    exact ⟨index, hroot, rfl, hdescent⟩
  · rintro ⟨index, hroot, rfl, hdescent⟩
    exact ⟨index, (ideal.mem_inversions_iff_bruhat_descent element index).mpr
      ⟨hroot, hdescent⟩, rfl⟩

/-- The number of descending Hessenberg neighbors is the paper's H-length. -/
theorem card_image_inversions (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ((ideal.inversions element).image (fun index => element * rootReflection index)).card =
      ideal.length element := by
  classical
  exact Finset.card_image_of_injective _ (inversion_neighbor_injective element)

/-- Every root of H is an H-inversion of the longest element. -/
theorem inversions_alternatingWord_top (ideal : HessenbergSpace n hthree) :
    ideal.inversions ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n)) = ideal.roots := by
  classical
  rw [inversions, _root_.Schubert.Dihedral.IndexedInversions.right_top, Finset.inter_univ]

/-- The longest element has H-length equal to the number of roots of H. -/
theorem length_alternatingWord_top (ideal : HessenbergSpace n hthree) :
    ideal.length ((coxeterSystem n hthree).wordProd
      (CoxeterSystem.alternatingWord 0 1 n)) = ideal.roots.card := by
  rw [length, ideal.inversions_alternatingWord_top]

end Schubert.DihedralSplines.HessenbergSpace
