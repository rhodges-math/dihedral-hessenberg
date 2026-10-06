import Schubert.Dihedral.RootLatticeRescaling

/-! # The equal-length triangular root configuration -/

noncomputable section

namespace Schubert.Dihedral.RootLattice

/-- The A configuration is the identity radial realization of its unit directions. -/
def a2Rescaling : Rescaling a2 3 where
  radius := fun _ => 1
  positive := by intro _; norm_num
  carrier := by
    rw [a2_positive]
    ext vector
    constructor
    · rintro ⟨index, rfl⟩
      exact ⟨positiveRootEquiv 3 index, by simp⟩
    · rintro ⟨alpha, rfl⟩
      simpa only [one_smul] using alpha.property
  conjugate := by intros; rfl

/-- The alternating numbering of the A positive roots is the simple pair and their sum. -/
theorem a2_numbered (index : PositiveRootIndex 3) :
    positiveRoot 3 index = ![a2.first, a2.second, a2.first + a2.second] index := by
  fin_cases index
  · change _ = (simpleRoot 3 (by decide) 0).val
    rw [simpleRoot_zero, positiveRootEquiv_val]
    rfl
  · change _ = (simpleRoot 3 (by decide) 1).val
    rw [simpleRoot_one, positiveRootEquiv_val]
    rfl
  · rw [a2_coordinates.1, a2_coordinates.2]
    norm_num [positiveRoot, rootAngle, unitRootAt, Real.cos_pi_div_three,
      Real.sin_pi_div_three, Pi.add_apply]

/-- The signed A roots have the standard six unit coordinates. -/
theorem a2_roots : a2.roots =
    {![1, 0], ![-1 / 2, Real.sqrt 3 / 2], ![1 / 2, Real.sqrt 3 / 2],
      ![-1, 0], ![1 / 2, -Real.sqrt 3 / 2], ![-1 / 2, -Real.sqrt 3 / 2]} := by
  have hpositive : a2.positive =
      {![1, 0], ![-1 / 2, Real.sqrt 3 / 2], ![1 / 2, Real.sqrt 3 / 2]} := by
    change {a2.first, a2.second, a2.first + a2.second} = _
    rw [a2_coordinates.1, a2_coordinates.2]
    norm_num [Matrix.add_cons]
  rw [roots, hpositive]
  ext vector
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_eq_iff_eq_neg]
  norm_num only [Matrix.neg_cons, Matrix.neg_empty, neg_neg, neg_zero, neg_div]
  tauto

/-- The two unit A simple roots have Cartan entries minus one. -/
theorem a2_cartan :
    2 * realBilinearForm a2.second a2.first / realBilinearForm a2.first a2.first = -1 ∧
      2 * realBilinearForm a2.first a2.second / realBilinearForm a2.second a2.second = -1 := by
  rw [a2_coordinates.1, a2_coordinates.2]
  norm_num [realBilinearForm]
  ring_nf
  norm_num [Real.sq_sqrt]

set_option maxHeartbeats 500000 in
/-- All signed A root-coroot pairings are integral. -/
theorem a2_integral (normal vector : RealPlane) (hnormal : normal ∈ a2.roots)
    (hvector : vector ∈ a2.roots) :
    ∃ integer : ℤ, 2 * realBilinearForm vector normal /
      realBilinearForm normal normal = (integer : ℝ) := by
  rw [a2_roots] at hnormal hvector
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm]
  all_goals (try ring_nf)
  all_goals norm_num [Real.sq_sqrt]
  all_goals solve
    | refine ⟨-2, ?_⟩; norm_num
    | refine ⟨-1, ?_⟩; norm_num
    | refine ⟨0, ?_⟩; norm_num
    | refine ⟨1, ?_⟩; norm_num
    | refine ⟨2, ?_⟩; norm_num

end Schubert.Dihedral.RootLattice
