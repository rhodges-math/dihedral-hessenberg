import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.DihedralSplines.PaperGraph
import Schubert.DihedralSplines.HessenbergSimpleEdgeRanges

/-! # Hessenberg inversion and edge changes at simple-vector ascents -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem edge_indices (ideal : HessenbergIdeal n hthree) (simple : Fin 2)
    (element : DihedralGroup n) :
    (element, simpleReflection n simple * element) ∈ ideal.toRootSubset.edges ↔
      ∃ index ∈ ideal.indexed.roots,
        simpleReflection n simple * element = element * rootReflection index := by
  rw [RootSubset.mem_edges]
  constructor
  · rintro ⟨alpha, halpha, heq⟩
    refine ⟨alpha.index, ?_, heq⟩
    rw [ideal.mem_indexed, PositiveRoot.index_val]
    exact halpha
  · rintro ⟨index, hindex, heq⟩
    refine ⟨positiveRootEquiv n index, ?_, ?_⟩
    · exact (ideal.mem_indexed index).mp hindex
    · simpa only [PositiveRoot.reflection_equiv] using heq

private theorem ascent_length (simple : Fin 2) (element : DihedralGroup n)
    (hup : BruhatLE n hthree element (simpleReflection n simple * element))
    (hne : element ≠ simpleReflection n simple * element) :
    Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1 := by
  have hstrict := ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hup).resolve_left hne
  have hstep := (coxeterSystem n hthree).length_simple_mul element simple
  rw [coxeterSystem_simple] at hstep
  change Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
    Schubert.Dihedral.length n hthree element + 1 ∨
    Schubert.Dihedral.length n hthree (simpleReflection n simple * element) + 1 =
      Schubert.Dihedral.length n hthree element at hstep
  omega

private theorem exists_simple {alpha : PositiveRoot n}
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
  rcases hsimple with hfirst | hsecond
  · exact ⟨0, hfirst⟩
  · exact ⟨1, hsecond⟩

/-- A simple-vector ascent outside the edge set preserves the H-inversion set. -/
theorem inversions_no_edge (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n) (hup : BruhatLE n hthree element (alpha.reflection * element))
    (hne : element ≠ alpha.reflection * element)
    (hnot : (element, alpha.reflection * element) ∉ ideal.toRootSubset.edges) :
    ideal.toRootSubset.inversions (alpha.reflection * element) =
      ideal.toRootSubset.inversions element := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hup hne hnot ⊢
  have hset := ideal.indexed.inversions_no_edge simple
    (simpleRoot n hthree simple).index element (simpleRoot_reflection n hthree simple)
    (ascent_length simple element hup hne) (((edge_indices ideal simple element).not).mp hnot)
  rw [← ideal.image_inversions, hset, ideal.image_inversions]

/-- A simple-vector ascent along an edge increases H-length by one. -/
theorem length_edge (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n) (hup : BruhatLE n hthree element (alpha.reflection * element))
    (hne : element ≠ alpha.reflection * element)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges) :
    ideal.toRootSubset.length element + 1 =
      ideal.toRootSubset.length (alpha.reflection * element) := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hup hne hedge ⊢
  rw [ideal.length_indexed, ideal.length_indexed]
  exact (ideal.indexed.length_simple_left_ascent_of_edge simple
    (simpleRoot n hthree simple).index element (simpleRoot_reflection n hthree simple)
    (ascent_length simple element hup hne) ((edge_indices ideal simple element).mp hedge)).symm

/-- A simple-vector ascent edge forces the lower or upper range of simple edges. -/
theorem edge_range (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n) (hup : BruhatLE n hthree element (alpha.reflection * element))
    (hne : element ≠ alpha.reflection * element)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges) :
    if 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n then
      ∀ vertex, Schubert.Dihedral.length n hthree vertex ≤
        Schubert.Dihedral.length n hthree element →
          (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges
    else ∀ vertex, Schubert.Dihedral.length n hthree element <
      Schubert.Dihedral.length n hthree vertex →
        (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hup hne hedge ⊢
  have hrange := ideal.indexed.simple_edge_range_of_bruhat_ascent simple element hup hne
    ((edge_indices ideal simple element).mp hedge)
  split_ifs with hhalf
  · rw [ite_eq_left hhalf] at hrange
    exact fun vertex hvertex => (edge_indices ideal simple vertex).mpr (hrange vertex hvertex)
  · rw [ite_eq_right hhalf] at hrange
    exact fun vertex hvertex => (edge_indices ideal simple vertex).mpr (hrange vertex hvertex)

/-- A lower-half simple-vector edge has full canonical inversion degree. -/
theorem length_full (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n) (hup : BruhatLE n hthree element (alpha.reflection * element))
    (hne : element ≠ alpha.reflection * element)
    (hhalf : 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges) :
    ideal.toRootSubset.length element = Schubert.Dihedral.length n hthree element := by
  obtain ⟨simple, rfl⟩ := exists_simple hsimple
  rw [simpleRoot_reflection] at hup hne hedge
  rw [ideal.length_indexed]
  exact ideal.indexed.length_full_bruhat simple element
    hup hne hhalf ((edge_indices ideal simple element).mp hedge)

end Schubert.DihedralSplines.HessenbergIdeal
