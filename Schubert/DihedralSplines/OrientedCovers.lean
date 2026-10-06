import Schubert.DihedralSplines.OrientedGraph
import Mathlib.Order.Cover

/-! # Cover relations of length-oriented endpoint graphs -/

namespace Schubert.Dihedral.RootSubset

/-- Every cover in oriented reachability is already an oriented endpoint edge. -/
theorem covBy_edge {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (source target : DihedralGroup n)
    (hcover : @CovBy _ (selected.partialOrder hthree).toLT source target) :
    (source, target) ∈ selected.orientedEdges hthree := by
  have hpath := (selected.partialOrder_lt hthree source target).mp hcover.1
  cases hpath with
  | single hedge => exact hedge
  | @tail middle finish previous hedge =>
    exact False.elim (hcover.2
      ((selected.partialOrder_lt hthree source middle).mpr previous)
      ((selected.partialOrder_lt hthree middle target).mpr (.single hedge)))

/-- An oriented edge increasing canonical length by one is a reachability cover. -/
theorem covBy_of_length_succ {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (source target : DihedralGroup n)
    (hedge : (source, target) ∈ selected.orientedEdges hthree)
    (hlength : Schubert.Dihedral.length n hthree target =
      Schubert.Dihedral.length n hthree source + 1) :
    @CovBy _ (selected.partialOrder hthree).toLT source target := by
  refine ⟨(selected.partialOrder_lt hthree source target).mpr (.single hedge), ?_⟩
  intro middle hfirst hsecond
  have hlow := selected.directed_length_lt hthree
    ((selected.partialOrder_lt hthree source middle).mp hfirst)
  have hupp := selected.directed_length_lt hthree
    ((selected.partialOrder_lt hthree middle target).mp hsecond)
  omega

end Schubert.Dihedral.RootSubset
