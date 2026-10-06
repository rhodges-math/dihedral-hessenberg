import Schubert.DihedralSplines.HessenbergSymmetry

/-! # Extremal Hessenberg degrees

Containing both simple roots forces H-length zero only at the identity. Longest
element symmetry then forces maximal H-length only at the longest vertex.
-/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The identity is the unique vertex of H-length zero. -/
theorem length_eq_zero_iff (ideal : HessenbergSpace n hthree) (element : DihedralGroup n) :
    ideal.length element = 0 ↔ element = 1 := by
  constructor
  · intro hzero
    by_contra hne
    obtain ⟨generator, hdescent⟩ :=
      (coxeterSystem n hthree).exists_rightDescent_of_ne_one hne
    have hdecrease : Schubert.Dihedral.length n hthree
        (element * simpleReflection n generator) < Schubert.Dihedral.length n hthree element := by
      change (coxeterSystem n hthree).length (element * simpleReflection n generator) <
        (coxeterSystem n hthree).length element
      simpa only [CoxeterSystem.IsRightDescent, coxeterSystem_simple] using hdescent
    have hexists : ∃ index, index ∈ ideal.inversions element := by
      fin_cases generator
      · change Schubert.Dihedral.length n hthree (element * simpleReflection n 0) <
          Schubert.Dihedral.length n hthree element at hdecrease
        rw [simpleReflection_zero] at hdecrease
        refine ⟨firstSimpleRootIndex n hthree, ?_⟩
        rw [ideal.mem_inversions]
        refine ⟨ideal.first_mem, ?_⟩
        simpa only [firstSimpleRootIndex, rootReflection_first] using
          hdecrease
      · change Schubert.Dihedral.length n hthree (element * simpleReflection n 1) <
          Schubert.Dihedral.length n hthree element at hdecrease
        rw [simpleReflection_one] at hdecrease
        refine ⟨secondSimpleRootIndex n hthree, ?_⟩
        rw [ideal.mem_inversions]
        refine ⟨ideal.second_mem, ?_⟩
        simpa only [secondSimpleRootIndex, rootReflection_second] using
          hdecrease
    obtain ⟨index, hindex⟩ := hexists
    have hempty : ideal.inversions element = ∅ := Finset.card_eq_zero.mp hzero
    rw [hempty] at hindex
    exact Finset.notMem_empty index hindex
  · rintro rfl
    exact ideal.length_one

/-- The longest vertex is the unique vertex of maximal H-length. -/
theorem length_eq_card_roots_iff (ideal : HessenbergSpace n hthree)
    (element : DihedralGroup n) :
    ideal.length element = ideal.roots.card ↔ element =
      (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n) := by
  let top := (coxeterSystem n hthree).wordProd (CoxeterSystem.alternatingWord 0 1 n)
  have hinv : top⁻¹ = top := alternatingWord_top_inv n hthree
  constructor
  · intro hmax
    have hsum := ideal.length_alternatingWord_top_mul_add element
    change ideal.length (top * element) + ideal.length element = ideal.roots.card at hsum
    have hzero : ideal.length (top * element) = 0 := by omega
    have heq := (ideal.length_eq_zero_iff (top * element)).mp hzero
    have hresult : element = top⁻¹ := eq_inv_of_mul_eq_one_right heq
    exact hresult.trans hinv
  · rintro rfl
    exact ideal.length_alternatingWord_top

end Schubert.DihedralSplines.HessenbergSpace
