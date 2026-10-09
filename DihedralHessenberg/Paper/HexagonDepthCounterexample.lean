import DihedralHessenberg.Paper.HexagonSignChambers

/-! # A four-vector depth-order ideal that cannot be a cone ideal after changing chamber -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- The four-vector depth-order ideal consists of positive vectors and contains both simples. -/
theorem six_lower_simple_pair :
    sixLowerRoots ⊆ positiveRoots 6 ∧
      (simpleRoot 6 (by decide) 0).val ∈ sixLowerRoots ∧
        (simpleRoot 6 (by decide) 1).val ∈ sixLowerRoots := by
  refine ⟨?_, ?_, ?_⟩
  · intro vector hvector
    simp only [sixLowerRoots, Set.mem_insert_iff, Set.mem_singleton_iff] at hvector
    rcases hvector with rfl | rfl | rfl | rfl
    all_goals exact (positiveRootEquiv 6 _).property
  · rw [simpleRoot_zero]
    simp [sixLowerRoots, firstSimpleRootIndex]
  · rw [simpleRoot_one]
    simp [sixLowerRoots, secondSimpleRootIndex]

/-- The four-vector subset has cardinality four. -/
theorem six_lower_card : sixLowerRoots.ncard = 4 := by
  rw [← six_chamber_bisector]
  exact six_chamber_card _

/-- An increasing-depth lower subset is not a cone ideal in any chamber. -/
theorem six_depth_counterexample :
    sixLowerRoots ⊆ positiveRoots 6 ∧ sixLowerRoots.ncard = 4 ∧
    (simpleRoot 6 (by decide) 0).val ∈ sixLowerRoots ∧
    (simpleRoot 6 (by decide) 1).val ∈ sixLowerRoots ∧
    (∀ alpha beta : PositiveRoot 6,
      Relation.ReflTransGen (DepthStep (by decide)) alpha beta →
        beta.val ∈ sixLowerRoots → alpha.val ∈ sixLowerRoots) ∧
    ∀ (data : Separator 6) (frame : data.Frame),
      ¬((∀ alpha beta : data.Positive,
          (∃ first second : ℝ, 0 ≤ first ∧ 0 ≤ second ∧
            beta.val - alpha.val = first • (frame.first (by decide)).val +
              second • (frame.second (by decide)).val) →
          beta.val ∈ sixChamberRoots data → alpha.val ∈ sixChamberRoots data) ∧
        (frame.first (by decide)).val ∈ sixChamberRoots data ∧
        (frame.second (by decide)).val ∈ sixChamberRoots data) := by
  refine ⟨six_lower_simple_pair.1, six_lower_card, six_lower_simple_pair.2.1,
    six_lower_simple_pair.2.2, six_depth_lower_paths, ?_⟩
  intro data frame hproperties
  exact six_no_chamber_ideal data frame hproperties.1 hproperties.2.1 hproperties.2.2

end Schubert.DihedralSplines
