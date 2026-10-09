import DihedralHessenberg.Paper.OrientedGraph
import DihedralHessenberg.Dihedral.RootReflectionVectors

/-! # Every edge of the Cayley graph is oriented

The endpoints `w` and `w s_α` of an edge have different lengths, so orienting edges from smaller
to larger length directs every edge, in exactly one of its two directions.
-/

namespace Schubert.Dihedral.RootSubset

/-- The two endpoints of an edge have different lengths. -/
theorem edge_length_ne {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    {pair : DihedralGroup n × DihedralGroup n} (hedge : pair ∈ selected.edges) :
    Schubert.Dihedral.length n hthree pair.1 ≠ Schubert.Dihedral.length n hthree pair.2 := by
  obtain ⟨alpha, -, htarget⟩ := (selected.mem_edges pair).mp hedge
  have hne := (alpha.isReflection hthree).length_mul_left_ne pair.1
  change Schubert.Dihedral.length n hthree (pair.1 * alpha.reflection) ≠
    Schubert.Dihedral.length n hthree pair.1 at hne
  rw [htarget]
  exact hne.symm

/-- Exactly one of an edge and its reversal is oriented from smaller to larger length. -/
theorem oriented_xor_reverse {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    {source target : DihedralGroup n} (hedge : (source, target) ∈ selected.edges) :
    Xor ((source, target) ∈ selected.orientedEdges hthree)
      ((target, source) ∈ selected.orientedEdges hthree) := by
  have hne := selected.edge_length_ne hthree hedge
  have hreverse := selected.edge_symm hedge
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ⟨⟨hedge, hlt⟩, fun hback => lt_asymm hlt hback.2⟩
  · exact Or.inr ⟨⟨hreverse, hgt⟩, fun hforward => lt_asymm hgt hforward.2⟩

end Schubert.Dihedral.RootSubset
