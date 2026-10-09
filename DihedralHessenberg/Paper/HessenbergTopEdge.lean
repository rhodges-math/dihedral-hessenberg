import DihedralHessenberg.Paper.RootConjugateEdge
import DihedralHessenberg.Paper.UpperConnectivity
import DihedralHessenberg.Dihedral.RootReflectionLengthVectors

/-! # Selected simple ascents into the longest vertex -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- Every simple ascent into the longest element is a Hessenberg edge. -/
theorem edge_to_top {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (vertex : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (htop : alpha.reflection * vertex = longestElement n hthree) :
    (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges := by
  let : NeZero n := ⟨by omega⟩
  have hfull := RootSubset.full_left_edge n hthree alpha vertex
  obtain ⟨gamma, _, hneighbor⟩ := ((RootSubset.full n).mem_edges _).mp hfull
  have htopLength := (length_eq_longest n hthree (alpha.reflection * vertex)).mpr htop
  have hlength : length n hthree vertex = n - 1 := by omega
  have hup : BruhatLE n hthree vertex (alpha.reflection * vertex) :=
    bruhatLE_of_length_lt n hthree (by omega)
  have hne : vertex ≠ alpha.reflection * vertex := by
    intro heq
    have := congrArg (length n hthree) heq
    omega
  have hreflection := alpha.ascent_length hthree gamma hsimple vertex hup hne hneighbor
  rw [ite_eq_right (by omega)] at hreflection
  have hcard := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed] at hcard
  exact ⟨gamma, ideal.selected_of_short gamma (by omega), hneighbor⟩

end Schubert.DihedralSplines.HessenbergIdeal
