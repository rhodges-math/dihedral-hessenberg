import Schubert.Dihedral.CrystallographicCoordinates

/-! # Integral root-coroot pairings of the G configuration -/

namespace Schubert.Dihedral.RootLattice

set_option maxHeartbeats 1200000 in
/-- Every pair of signed G vectors has an integral root-coroot pairing. -/
theorem g2_integral (normal vector : RealPlane) (hnormal : normal ∈ g2.roots)
    (hvector : vector ∈ g2.roots) :
    ∃ integer : ℤ, 2 * realBilinearForm vector normal /
      realBilinearForm normal normal = (integer : ℝ) := by
  rw [g2_roots] at hnormal hvector
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm]
  all_goals (try ring_nf)
  all_goals norm_num [Real.sq_sqrt]
  all_goals solve
    | refine ⟨-3, ?_⟩; norm_num
    | refine ⟨-2, ?_⟩; norm_num
    | refine ⟨-1, ?_⟩; norm_num
    | refine ⟨0, ?_⟩; norm_num
    | refine ⟨1, ?_⟩; norm_num
    | refine ⟨2, ?_⟩; norm_num
    | refine ⟨3, ?_⟩; norm_num

end Schubert.Dihedral.RootLattice
