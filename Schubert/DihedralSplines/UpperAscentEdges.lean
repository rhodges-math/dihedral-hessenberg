import Schubert.DihedralSplines.HessenbergSimpleEdgeRanges

/-! # Simple ascent edges above an upper-half Hessenberg vertex -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem rootReflection_eq_conjugate_of_neighbor
    (simple : Fin 2) (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hneighbor : simpleReflection n simple * element = element * rootReflection index) :
    rootReflection index = element⁻¹ * simpleReflection n simple * element := by
  have heq := congrArg (fun value => element⁻¹ * value) hneighbor
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using heq.symm

/-- Every simple ascent above an upper-half vertex is an edge under the fixed-edge hypothesis. -/
theorem simple_ascent_edge_above_upper_half (ideal : HessenbergSpace n hthree)
    (fixedSimple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n fixedSimple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : n < 2 * Schubert.Dihedral.length n hthree element + 1)
    (hEdges : ∀ vertex, BruhatLE n hthree element vertex →
      ∃ index ∈ ideal.roots,
        simpleReflection n fixedSimple * vertex = vertex * rootReflection index)
    (vertex : DihedralGroup n) (hvertex : BruhatLE n hthree element vertex)
    (simple : Fin 2)
    (hvertexAscent : Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) =
      Schubert.Dihedral.length n hthree vertex + 1) :
    ∃ index ∈ ideal.roots,
      simpleReflection n simple * vertex = vertex * rootReflection index := by
  have hEdge := hEdges element (bruhatLE_refl n hthree element)
  by_cases heq : vertex = element
  · subst vertex
    have hpositive : 0 < Schubert.Dihedral.length n hthree element := by omega
    have hshort : Schubert.Dihedral.length n hthree element < n := by
      have hbound := length_le_polygon_parameter n hthree
        (simpleReflection n fixedSimple * element)
      omega
    obtain ⟨ascent, _, hunique⟩ :=
      existsUnique_simple_left_ascent n hthree element hpositive hshort
    have hsimple : simple = fixedSimple :=
      (hunique simple hvertexAscent).trans (hunique fixedSimple hascent).symm
    simpa only [hsimple] using hEdge
  have hstrict := ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hvertex).resolve_left
    (Ne.symm heq)
  obtain ⟨second, hsecond, hneighbor⟩ := hEdge
  have hsecondConj := rootReflection_eq_conjugate_of_neighbor fixedSimple element second hneighbor
  have hsecondLength : Schubert.Dihedral.length n hthree (rootReflection second) =
      2 * (n - Schubert.Dihedral.length n hthree element) - 1 := by
    rw [hsecondConj,
      length_conjugate_simple_of_left_ascent n hthree fixedSimple element hascent,
        ite_eq_right (by omega)]
  have hreflection := ((coxeterSystem n hthree).isReflection_simple simple).conj vertex⁻¹
  rw [coxeterSystem_simple, inv_inv] at hreflection
  obtain ⟨first, hfirstConj⟩ :=
    (isReflection_iff_exists_rootReflection n hthree _).mp hreflection
  have hfirstNeighbor : simpleReflection n simple * vertex = vertex * rootReflection first := by
    rw [hfirstConj]
    group
  refine ⟨first, ideal.mem_roots_of_reflection_length_lt first second hsecond ?_, hfirstNeighbor⟩
  have hfirstBound := length_le_polygon_parameter n hthree (simpleReflection n simple * vertex)
  have hsecondBound := length_le_polygon_parameter n hthree
    (simpleReflection n fixedSimple * element)
  rw [hfirstConj, length_conjugate_simple_of_left_ascent n hthree simple vertex hvertexAscent,
    ite_eq_right (by omega), hsecondLength]
  omega

/-- Such a simple ascent edge persists at every strictly longer vertex. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.SimpleEdges.above_upper_ascent (ideal :
  HessenbergSpace n hthree)
    (fixedSimple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n fixedSimple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : n < 2 * Schubert.Dihedral.length n hthree element + 1)
    (hEdges : ∀ vertex, BruhatLE n hthree element vertex →
      ∃ index ∈ ideal.roots,
        simpleReflection n fixedSimple * vertex = vertex * rootReflection index)
    (vertex : DihedralGroup n) (hvertex : BruhatLE n hthree element vertex)
    (simple : Fin 2)
    (hvertexAscent : Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) =
      Schubert.Dihedral.length n hthree vertex + 1)
    (upper : DihedralGroup n)
    (hupper : Schubert.Dihedral.length n hthree vertex <
      Schubert.Dihedral.length n hthree upper) :
    ∃ index ∈ ideal.roots,
      simpleReflection n simple * upper = upper * rootReflection index := by
  have hEdge := ideal.simple_ascent_edge_above_upper_half fixedSimple element hascent hhalf
    hEdges vertex hvertex simple hvertexAscent
  have hlength := bruhatLE_length_le n hthree hvertex
  exact ideal.simple_edges_above_upper_half_ascent simple vertex hvertexAscent (by omega)
    hEdge upper hupper

end Schubert.DihedralSplines.HessenbergSpace
