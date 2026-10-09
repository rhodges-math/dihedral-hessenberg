import DihedralHessenberg.Dihedral.CrystallographicCoordinates

/-! # Signed planar coordinates and integral pairings of the C configuration -/

namespace Schubert.Dihedral.RootLattice

/-- The four C positive roots have their long-axis and short-diagonal coordinates. -/
theorem c2_positive : c2.positive =
    {![Real.sqrt 2, 0], ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2],
      ![Real.sqrt 2 / 2, Real.sqrt 2 / 2], ![0, Real.sqrt 2]} := by
  have hset : c2.positive = {c2.first, c2.second, c2.first + c2.second,
      c2.first + (2 : ℝ) • c2.second} := rfl
  rw [hset, c2_first, c2_second]
  have hsum : (![Real.sqrt 2, 0] : RealPlane) +
      ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2] = ![Real.sqrt 2 / 2, Real.sqrt 2 / 2] := by
    apply realPlane_ext <;> simp only [Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one] <;> ring
  have hdouble : (![Real.sqrt 2, 0] : RealPlane) +
      (2 : ℝ) • ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2] = ![0, Real.sqrt 2] := by
    apply realPlane_ext <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  rw [hsum, hdouble]

/-- The eight signed C roots have their standard planar coordinates. -/
theorem c2_roots : c2.roots =
    {![Real.sqrt 2, 0], ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2],
      ![Real.sqrt 2 / 2, Real.sqrt 2 / 2], ![0, Real.sqrt 2],
      ![-Real.sqrt 2, 0], ![Real.sqrt 2 / 2, -Real.sqrt 2 / 2],
      ![-Real.sqrt 2 / 2, -Real.sqrt 2 / 2], ![0, -Real.sqrt 2]} := by
  rw [roots, c2_positive]
  ext vector
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_eq_iff_eq_neg]
  norm_num only [Matrix.neg_cons, Matrix.neg_empty, neg_neg, neg_zero, neg_div]
  tauto

set_option maxHeartbeats 800000 in
/-- All signed C root-coroot pairings are integral. -/
theorem c2_integral (normal vector : RealPlane) (hnormal : normal ∈ c2.roots)
    (hvector : vector ∈ c2.roots) :
    ∃ integer : ℤ, 2 * realBilinearForm vector normal /
      realBilinearForm normal normal = (integer : ℝ) := by
  rw [c2_roots] at hnormal hvector
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
