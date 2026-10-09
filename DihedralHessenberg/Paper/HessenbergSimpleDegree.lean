import DihedralHessenberg.Dihedral.GeometricAscent
import DihedralHessenberg.Paper.HessenbergInversions

/-! # Hessenberg inversion changes along simple left ascents -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The unique new right inversion indexes the simple neighbor and updates H-inversions. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.simple_inversion_update (ideal :
  HessenbergSpace n hthree)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1) :
    ∃ image : PositiveRootIndex n,
      simpleReflection n simple * element = element * rootReflection image ∧
        image ∉ ideal.inversions element ∧
          ideal.inversions (simpleReflection n simple * element) =
            if image ∈ ideal.roots then insert image (ideal.inversions element)
              else ideal.inversions element := by
  classical
  let : NeZero n := ⟨by omega⟩
  obtain ⟨image, himage, hset, hnot⟩ :=
    _root_.Schubert.Dihedral.IndexedInversions.right_ascent_image
    n hthree simple index element hreflection hascent
  have hconj := rootReflection_of_positive_image n element⁻¹ index image himage
  rw [inv_inv, hreflection] at hconj
  have hneighbor : simpleReflection n simple * element = element * rootReflection image := by
    rw [hconj]
    group
  refine ⟨image, hneighbor, ?_, ?_⟩
  · exact fun h => hnot (ideal.inversions_subset_rightInversions element h)
  · ext previous
    by_cases hmember : image ∈ ideal.roots
    · simp only [ite_eq_left hmember, inversions, hset, Finset.mem_inter,
        Finset.mem_insert]
      aesop
    · simp only [ite_eq_right hmember, inversions, hset, Finset.mem_inter,
        Finset.mem_insert]
      aesop

private theorem simple_neighbor_edge_iff (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (element : DihedralGroup n) (image : PositiveRootIndex n)
    (hneighbor : simpleReflection n simple * element = element * rootReflection image) :
    (∃ previous ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection previous) ↔
        image ∈ ideal.roots := by
  constructor
  · rintro ⟨previous, hprevious, heq⟩
    have hindices := rootReflection_injective n
      (mul_left_cancel (hneighbor.symm.trans heq))
    exact hindices.symm ▸ hprevious
  · intro hmember
    exact ⟨image, hmember, hneighbor⟩

/-- A simple ascent outside the Hessenberg edge set preserves H-inversions. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.inversions_no_edge (ideal : HessenbergSpace
  n hthree)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hnotEdge : ¬∃ previous ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection previous) :
    ideal.inversions (simpleReflection n simple * element) = ideal.inversions element := by
  obtain ⟨image, hneighbor, _, hupdate⟩ :=
    ideal.simple_inversion_update simple index element hreflection hascent
  have hnot := ((simple_neighbor_edge_iff ideal simple element image hneighbor).not).mp hnotEdge
  rw [hupdate, ite_eq_right hnot]

/-- A simple ascent along a Hessenberg edge raises H-length by one. -/
theorem length_simple_left_ascent_of_edge (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (index : PositiveRootIndex n) (element : DihedralGroup n)
    (hreflection : rootReflection index = simpleReflection n simple)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hEdge : ∃ previous ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection previous) :
    ideal.length (simpleReflection n simple * element) = ideal.length element + 1 := by
  classical
  obtain ⟨image, hneighbor, hnot, hupdate⟩ :=
    ideal.simple_inversion_update simple index element hreflection hascent
  have hmember := (simple_neighbor_edge_iff ideal simple element image hneighbor).mp hEdge
  rw [length, hupdate, ite_eq_left hmember, Finset.card_insert_of_notMem hnot]
  rfl

end Schubert.DihedralSplines.HessenbergSpace
