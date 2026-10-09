import DihedralHessenberg.Paper.RootConjugateEdge
import DihedralHessenberg.Paper.FullUpperBoundary

/-! # Counts of ascending endpoint neighbors -/

namespace Schubert.Dihedral.RootSubset

/-- Selected endpoint neighbors have distinct canonical lengths. -/
theorem edge_lengths_ne {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (source target : DihedralGroup n) (hedge : (source, target) ∈ selected.edges) :
    Schubert.Dihedral.length n hthree source ≠ Schubert.Dihedral.length n hthree target := by
  obtain ⟨alpha, _, hneighbor⟩ := (selected.mem_edges _).mp hedge
  have hfull : (source, target) ∈ (full n).edges :=
    ⟨alpha, alpha.property, hneighbor⟩
  have hparity := (full_edge_parity n hthree source target).mp hfull
  exact fun heq => hparity (congrArg (fun degree => degree % 2) heq)

/-- Ascending endpoint neighbors are counted by the complementary inversion statistic. -/
theorem ascending_card {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (source : DihedralGroup n) :
    {target : DihedralGroup n | (source, target) ∈ selected.edges ∧
      Schubert.Dihedral.length n hthree source < Schubert.Dihedral.length n hthree target}.ncard =
        selected.carrier.ncard - selected.length source := by
  classical
  let : NeZero n := ⟨by omega⟩
  let neighbors : Set (DihedralGroup n) := {target | (source, target) ∈ selected.edges}
  let lower : Set (DihedralGroup n) := {target | (source, target) ∈ selected.edges ∧
    Schubert.Dihedral.length n hthree target < Schubert.Dihedral.length n hthree source}
  let higher : Set (DihedralGroup n) := {target | (source, target) ∈ selected.edges ∧
    Schubert.Dihedral.length n hthree source < Schubert.Dihedral.length n hthree target}
  have hsplit : neighbors = lower ∪ higher := by
    ext target
    simp only [neighbors, lower, higher, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro hedge
      have hne := selected.edge_lengths_ne hthree source target hedge
      by_cases hless : Schubert.Dihedral.length n hthree target <
          Schubert.Dihedral.length n hthree source
      · exact Or.inl ⟨hedge, hless⟩
      · exact Or.inr ⟨hedge, by omega⟩
    · rintro (h | h) <;> exact h.1
  have hdisjoint : Disjoint lower higher := by
    apply Set.disjoint_left.mpr
    intro target hlower hhigher
    have := hlower.2
    have := hhigher.2
    omega
  have hcount : selected.carrier.ncard = selected.length source + higher.ncard := by
    calc
      _ = neighbors.ncard := (selected.neighbor_card source).symm
      _ = (lower ∪ higher).ncard := congrArg Set.ncard hsplit
      _ = lower.ncard + higher.ncard := Set.ncard_union_eq hdisjoint
      _ = _ := by rw [selected.descending_card hthree]
  change higher.ncard = _
  omega

end Schubert.Dihedral.RootSubset
