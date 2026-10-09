import DihedralHessenberg.Dihedral.RightWeak
import DihedralHessenberg.Paper.OrientedGraph

/-! # Right weak order from the simple-root endpoint graph -/

namespace Schubert.Dihedral.RootSubset

private theorem simple_oriented_step {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (hroots : selected.carrier =
      {(simpleRoot n hthree 0).val, (simpleRoot n hthree 1).val})
    (source target : DihedralGroup n) :
    (source, target) ∈ selected.orientedEdges hthree ↔
      ∃ simple : Fin 2, target = source * (coxeterSystem n hthree).simple simple ∧
        (coxeterSystem n hthree).length source < (coxeterSystem n hthree).length target := by
  constructor
  · rintro ⟨hedge, hlength⟩
    obtain ⟨alpha, hselected, htarget⟩ := (selected.mem_edges _).mp hedge
    change alpha.val ∈ selected.carrier at hselected
    rw [hroots, Set.mem_insert_iff, Set.mem_singleton_iff] at hselected
    change target = source * alpha.reflection at htarget
    rcases hselected with hfirst | hsecond
    · have halpha : alpha = simpleRoot n hthree 0 := Subtype.ext hfirst
      refine ⟨0, ?_, hlength⟩
      simpa only [halpha, simpleRoot_reflection, coxeterSystem_simple] using htarget
    · have halpha : alpha = simpleRoot n hthree 1 := Subtype.ext hsecond
      refine ⟨1, ?_, hlength⟩
      simpa only [halpha, simpleRoot_reflection, coxeterSystem_simple] using htarget
  · rintro ⟨simple, htarget, hlength⟩
    refine ⟨?_, hlength⟩
    apply (selected.mem_edges _).mpr
    refine ⟨simpleRoot n hthree simple, ?_, ?_⟩
    · change (simpleRoot n hthree simple).val ∈ selected.carrier
      rw [hroots]
      fin_cases simple <;> simp
    · change target = source * (simpleRoot n hthree simple).reflection
      simpa only [simpleRoot_reflection, coxeterSystem_simple] using htarget

/-- Reachability for exactly the two simple root vectors is canonical right weak order. -/
theorem simple_reachable {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (hroots : selected.carrier =
      {(simpleRoot n hthree 0).val, (simpleRoot n hthree 1).val})
    (source target : DihedralGroup n) :
    selected.reachable hthree source target ↔ RightWeakLE n hthree source target := by
  rw [rightWeakLE_path]
  change Relation.ReflTransGen
    (fun first second => (first, second) ∈ selected.orientedEdges hthree) source target ↔ _
  have hrelation : (fun first second => (first, second) ∈ selected.orientedEdges hthree) =
      (fun first second => ∃ simple : Fin 2,
        second = first * (coxeterSystem n hthree).simple simple ∧
          (coxeterSystem n hthree).length first < (coxeterSystem n hthree).length second) := by
    funext first second
    exact propext (simple_oriented_step hthree selected hroots first second)
  rw [hrelation]

end Schubert.Dihedral.RootSubset
