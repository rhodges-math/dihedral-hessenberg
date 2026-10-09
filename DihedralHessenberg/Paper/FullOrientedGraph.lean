import DihedralHessenberg.Paper.OrientedGraph
import DihedralHessenberg.Paper.UpperConnectivity

/-! # Canonical Bruhat order from the full reflection graph -/

namespace Schubert.Dihedral.RootSubset

/-- Full oriented endpoint edges are exactly canonical Bruhat reflection steps. -/
theorem full_oriented_step (n : ℕ) (hthree : 3 ≤ n)
    (source target : DihedralGroup n) :
    (source, target) ∈ (full n).orientedEdges hthree ↔
      (coxeterSystem n hthree).BruhatStep source target := by
  constructor
  · rintro ⟨hedge, hlength⟩
    obtain ⟨alpha, _, htarget⟩ := ((full n).mem_edges _).mp hedge
    change target = source * alpha.reflection at htarget
    refine ⟨source * alpha.reflection * source⁻¹,
      (alpha.isReflection hthree).conj source, ?_, hlength⟩
    rw [htarget]
    group
  · rintro ⟨reflection, hreflection, htarget, hlength⟩
    obtain ⟨alpha, halpha⟩ := (isReflection_iff_positiveRoot n hthree reflection).mp hreflection
    rw [← halpha] at htarget
    refine ⟨?_, hlength⟩
    rw [htarget]
    exact full_left_edge n hthree alpha source

/-- The partial order of the full graph is canonical strong Bruhat order. -/
theorem full_reachable (n : ℕ) (hthree : 3 ≤ n) (source target : DihedralGroup n) :
    (full n).reachable hthree source target ↔ BruhatLE n hthree source target := by
  change Relation.ReflTransGen
    (fun first second => (first, second) ∈ (full n).orientedEdges hthree) source target ↔
      Relation.ReflTransGen (coxeterSystem n hthree).BruhatStep source target
  have hrelation : (fun first second => (first, second) ∈ (full n).orientedEdges hthree) =
      (coxeterSystem n hthree).BruhatStep := by
    funext first second
    exact propext (full_oriented_step n hthree first second)
  rw [hrelation]

end Schubert.Dihedral.RootSubset
