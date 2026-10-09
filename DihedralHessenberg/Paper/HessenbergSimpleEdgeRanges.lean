import DihedralHessenberg.Dihedral.ConjugatedLength
import DihedralHessenberg.Dihedral.InversionBounds
import DihedralHessenberg.Dihedral.SimpleAscentRecognition
import DihedralHessenberg.Paper.RootLayerOrder
import DihedralHessenberg.Paper.HessenbergSimpleDegree

/-! # Hessenberg edge ranges from conjugated reflection length -/

namespace Schubert.DihedralSplines.HessenbergSpace

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem rootReflection_eq_conjugate_of_simple_neighbor
    (simple : Fin 2) (element : DihedralGroup n) (index : PositiveRootIndex n)
    (hneighbor : simpleReflection n simple * element = element * rootReflection index) :
    rootReflection index = element⁻¹ * simpleReflection n simple * element := by
  have heq := congrArg (fun value => element⁻¹ * value) hneighbor
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using heq.symm

private theorem exists_simple_neighbor_root (hthree : 3 ≤ n)
    (simple : Fin 2) (element : DihedralGroup n) :
    ∃ index : PositiveRootIndex n,
      simpleReflection n simple * element = element * rootReflection index := by
  have hreflection := ((coxeterSystem n hthree).isReflection_simple simple).conj element⁻¹
  rw [coxeterSystem_simple, inv_inv] at hreflection
  obtain ⟨index, hindex⟩ :=
    (isReflection_iff_exists_rootReflection n hthree _).mp hreflection
  refine ⟨index, ?_⟩
  rw [hindex]
  group

/-- An ideal contains every root whose reflection is shorter than a contained reflection. -/
theorem mem_roots_of_reflection_length_lt (ideal : HessenbergSpace n hthree)
    (first second : PositiveRootIndex n) (hsecond : second ∈ ideal.roots)
    (hshort : Schubert.Dihedral.length n hthree (rootReflection first) <
      Schubert.Dihedral.length n hthree (rootReflection second)) : first ∈ ideal.roots := by
  rw [length_rootReflection, length_rootReflection] at hshort
  apply ideal.lower ((rootLE_iff_eq_or_layer_lt n hthree first second).mpr
    (Or.inr (by omega))) hsecond

/-- A lower-half simple ascent edge forces all previous right inversions into H. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.right_inversions_below
    (ideal : HessenbergSpace n hthree) (simple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) :
    rightInversions n hthree element ⊆ ideal.roots := by
  obtain ⟨second, hsecond, hneighbor⟩ := hEdge
  have hconj : rootReflection second = element⁻¹ * simpleReflection n simple * element := by
    have heq := congrArg (fun value => element⁻¹ * value) hneighbor
    simpa only [← mul_assoc, inv_mul_cancel, one_mul] using heq.symm
  have hsecondLength : Schubert.Dihedral.length n hthree (rootReflection second) =
      2 * Schubert.Dihedral.length n hthree element + 1 := by
    rw [hconj, length_conjugate_simple_of_left_ascent n hthree simple element hascent,
      ite_eq_left hhalf]
  intro first hfirst
  have hbound := _root_.Schubert.Dihedral.IndexedRoots.length_bound_at_inversion n hthree element
    first hfirst
  apply ideal.mem_roots_of_reflection_length_lt first second hsecond
  omega

/-- Along a lower-half simple ascent edge, H-length equals canonical Coxeter length. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.length_full
    (ideal : HessenbergSpace n hthree) (simple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) :
    ideal.length element = Schubert.Dihedral.length n hthree element := by
  classical
  have hsubset := ideal.right_inversions_below
    simple element hascent hhalf hEdge
  rw [length, inversions, Finset.inter_eq_right.mpr hsubset, card_rightInversions]

/-- A lower-half simple ascent edge forces the same simple edge at every shorter vertex. -/
theorem simple_edges_below_lower_half_ascent (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index)
    (vertex : DihedralGroup n)
    (hvertex : Schubert.Dihedral.length n hthree vertex ≤
      Schubert.Dihedral.length n hthree element) :
    ∃ index ∈ ideal.roots,
      simpleReflection n simple * vertex = vertex * rootReflection index := by
  by_cases heq : vertex = element
  · simpa only [heq] using hEdge
  obtain ⟨second, hsecond, hneighbor⟩ := hEdge
  have hsecondConj := rootReflection_eq_conjugate_of_simple_neighbor simple element second hneighbor
  have hsecondLength : Schubert.Dihedral.length n hthree (rootReflection second) =
      2 * Schubert.Dihedral.length n hthree element + 1 := by
    rw [hsecondConj, length_conjugate_simple_of_left_ascent n hthree simple element hascent,
      ite_eq_left hhalf]
  obtain ⟨first, hfirstNeighbor⟩ := exists_simple_neighbor_root (hthree := hthree) simple vertex
  have hfirstConj :=
    rootReflection_eq_conjugate_of_simple_neighbor simple vertex first hfirstNeighbor
  refine ⟨first, ideal.mem_roots_of_reflection_length_lt first second hsecond ?_, hfirstNeighbor⟩
  have hstep := (coxeterSystem n hthree).length_simple_mul vertex simple
  rw [coxeterSystem_simple] at hstep
  change Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) =
      Schubert.Dihedral.length n hthree vertex + 1 ∨
    Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) + 1 =
      Schubert.Dihedral.length n hthree vertex at hstep
  rcases hstep with hvertexAscent | hvertexDescent
  · have hstrict : Schubert.Dihedral.length n hthree vertex <
        Schubert.Dihedral.length n hthree element := by
      by_contra hnot
      have hsame : Schubert.Dihedral.length n hthree vertex =
          Schubert.Dihedral.length n hthree element := by omega
      exact heq (_root_.Schubert.Dihedral.SimpleAscents.eq_of_length_eq n hthree simple vertex
        element
        hsame hvertexAscent hascent)
    rw [hfirstConj, length_conjugate_simple_of_left_ascent n hthree simple vertex hvertexAscent,
      ite_eq_left (by omega), hsecondLength]
    omega
  · rw [hfirstConj, length_conjugate_simple_of_left_descent n hthree simple vertex hvertexDescent,
      ite_eq_left (by omega), hsecondLength]
    omega

/-- An upper-half simple ascent edge forces the same simple edge at every longer vertex. -/
theorem simple_edges_above_upper_half_ascent (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (element : DihedralGroup n)
    (hascent : Schubert.Dihedral.length n hthree (simpleReflection n simple * element) =
      Schubert.Dihedral.length n hthree element + 1)
    (hhalf : n < 2 * Schubert.Dihedral.length n hthree element + 1)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index)
    (vertex : DihedralGroup n)
    (hvertex : Schubert.Dihedral.length n hthree element <
      Schubert.Dihedral.length n hthree vertex) :
    ∃ index ∈ ideal.roots,
      simpleReflection n simple * vertex = vertex * rootReflection index := by
  obtain ⟨second, hsecond, hneighbor⟩ := hEdge
  by_cases heq : vertex = simpleReflection n simple * element
  · subst vertex
    refine ⟨second, hsecond, ?_⟩
    rw [hneighbor, mul_assoc, rootReflection_mul_self, mul_one]
    rw [← hneighbor, ← mul_assoc, simpleReflection_mul_self, one_mul]
  have hsecondConj := rootReflection_eq_conjugate_of_simple_neighbor simple element second hneighbor
  have hsecondLength : Schubert.Dihedral.length n hthree (rootReflection second) =
      2 * (n - Schubert.Dihedral.length n hthree element) - 1 := by
    rw [hsecondConj, length_conjugate_simple_of_left_ascent n hthree simple element hascent,
      ite_eq_right (by omega)]
  obtain ⟨first, hfirstNeighbor⟩ := exists_simple_neighbor_root (hthree := hthree) simple vertex
  have hfirstConj :=
    rootReflection_eq_conjugate_of_simple_neighbor simple vertex first hfirstNeighbor
  refine ⟨first, ideal.mem_roots_of_reflection_length_lt first second hsecond ?_, hfirstNeighbor⟩
  have hstep := (coxeterSystem n hthree).length_simple_mul vertex simple
  rw [coxeterSystem_simple] at hstep
  change Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) =
      Schubert.Dihedral.length n hthree vertex + 1 ∨
    Schubert.Dihedral.length n hthree (simpleReflection n simple * vertex) + 1 =
      Schubert.Dihedral.length n hthree vertex at hstep
  have hvertexBound := length_le_polygon_parameter n hthree vertex
  have helementBound := length_le_polygon_parameter n hthree (simpleReflection n simple * element)
  rcases hstep with hvertexAscent | hvertexDescent
  · have hstrictBound := length_le_polygon_parameter n hthree (simpleReflection n simple * vertex)
    rw [hfirstConj, length_conjugate_simple_of_left_ascent n hthree simple vertex hvertexAscent,
      ite_eq_right (by omega), hsecondLength]
    omega
  · have hstrict : Schubert.Dihedral.length n hthree element + 1 <
        Schubert.Dihedral.length n hthree vertex := by
      by_contra hnot
      have hsame : Schubert.Dihedral.length n hthree vertex =
          Schubert.Dihedral.length n hthree (simpleReflection n simple * element) := by omega
      have hotherDescent : Schubert.Dihedral.length n hthree
          (simpleReflection n simple * (simpleReflection n simple * element)) + 1 =
            Schubert.Dihedral.length n hthree (simpleReflection n simple * element) := by
        rw [← mul_assoc, simpleReflection_mul_self, one_mul, hascent]
      exact heq (_root_.Schubert.Dihedral.SimpleDescents.eq_of_length_eq n hthree simple vertex
        (simpleReflection n simple * element) hsame hvertexDescent hotherDescent)
    rw [hfirstConj, length_conjugate_simple_of_left_descent n hthree simple vertex hvertexDescent,
      ite_eq_right (by omega), hsecondLength]
    omega

private theorem simple_left_ascent_of_bruhat (simple : Fin 2) (element : DihedralGroup n)
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

/-- A simple Bruhat ascent edge forces the paper's lower or upper simple-edge range. -/
theorem simple_edge_range_of_bruhat_ascent (ideal : HessenbergSpace n hthree)
    (simple : Fin 2) (element : DihedralGroup n)
    (hup : BruhatLE n hthree element (simpleReflection n simple * element))
    (hne : element ≠ simpleReflection n simple * element)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) :
    if 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n then
      ∀ vertex, Schubert.Dihedral.length n hthree vertex ≤
        Schubert.Dihedral.length n hthree element →
          ∃ index ∈ ideal.roots,
            simpleReflection n simple * vertex = vertex * rootReflection index
    else ∀ vertex, Schubert.Dihedral.length n hthree element <
      Schubert.Dihedral.length n hthree vertex →
        ∃ index ∈ ideal.roots,
          simpleReflection n simple * vertex = vertex * rootReflection index := by
  have hascent := simple_left_ascent_of_bruhat simple element hup hne
  split_ifs with hhalf
  · exact ideal.simple_edges_below_lower_half_ascent simple element hascent hhalf hEdge
  · exact ideal.simple_edges_above_upper_half_ascent simple element hascent (by omega) hEdge

/-- A lower-half simple Bruhat ascent edge has full canonical inversion degree. -/
theorem _root_.Schubert.DihedralSplines.HessenbergSpace.length_full_bruhat
    (ideal : HessenbergSpace n hthree) (simple : Fin 2) (element : DihedralGroup n)
    (hup : BruhatLE n hthree element (simpleReflection n simple * element))
    (hne : element ≠ simpleReflection n simple * element)
    (hhalf : 2 * Schubert.Dihedral.length n hthree element + 1 ≤ n)
    (hEdge : ∃ index ∈ ideal.roots,
      simpleReflection n simple * element = element * rootReflection index) :
    ideal.length element = Schubert.Dihedral.length n hthree element :=
  ideal.length_full simple element
    (simple_left_ascent_of_bruhat simple element hup hne) hhalf hEdge

end Schubert.DihedralSplines.HessenbergSpace
