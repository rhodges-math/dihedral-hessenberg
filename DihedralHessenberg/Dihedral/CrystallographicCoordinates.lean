import DihedralHessenberg.Dihedral.RootLattice
import DihedralHessenberg.Dihedral.RootRescaling

/-! # Coordinates and Cartan entries of the crystallographic rank-two configurations -/

namespace Schubert.Dihedral.RootLattice

/-- The C simple roots have the transposed B Cartan entries. -/
theorem c2_cartan :
    2 * realBilinearForm c2.second c2.first / realBilinearForm c2.first c2.first = -1 ∧
      2 * realBilinearForm c2.first c2.second / realBilinearForm c2.second c2.second = -2 := by
  have hsquare : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfirst : realBilinearForm c2.first c2.first = 2 := by
    rw [c2_first]
    norm_num [realBilinearForm, hsquare]
  have hsecond : realBilinearForm c2.second c2.second = 1 := by
    rw [c2_second]
    simp only [realBilinearForm, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  have hcross : realBilinearForm c2.second c2.first = -1 := by
    rw [c2_first, c2_second]
    simp only [realBilinearForm, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  have hreverse : realBilinearForm c2.first c2.second = -1 := by
    rw [c2_first, c2_second]
    simp only [realBilinearForm, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  rw [hfirst, hsecond, hcross, hreverse]
  norm_num

/-- The G simple roots have the integral Cartan entries minus three and minus one. -/
theorem g2_cartan :
    2 * realBilinearForm g2.second g2.first / realBilinearForm g2.first g2.first = -3 ∧
      2 * realBilinearForm g2.first g2.second / realBilinearForm g2.second g2.second = -1 := by
  have hsquare : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [g2_first, g2_second]
  norm_num [realBilinearForm, div_mul_div_comm, hsquare]

/-- The G positive roots have their standard planar coordinates. -/
theorem g2_positive : g2.positive =
    {![1, 0], ![-3 / 2, Real.sqrt 3 / 2], ![-1 / 2, Real.sqrt 3 / 2],
      ![1 / 2, Real.sqrt 3 / 2], ![3 / 2, Real.sqrt 3 / 2], ![0, Real.sqrt 3]} := by
  have hset : g2.positive = {g2.first, g2.second, g2.first + g2.second,
      (2 : ℝ) • g2.first + g2.second, (3 : ℝ) • g2.first + g2.second,
      (3 : ℝ) • g2.first + (2 : ℝ) • g2.second} := rfl
  rw [hset, g2_first, g2_second]
  norm_num [Matrix.add_cons, Matrix.smul_cons]
  have hdouble : (2 : ℝ) * (Real.sqrt 3 / 2) = Real.sqrt 3 := by ring
  rw [hdouble]

/-- The complete G roots are the standard twelve signed planar vectors. -/
theorem g2_roots : g2.roots =
    {![1, 0], ![-3 / 2, Real.sqrt 3 / 2], ![-1 / 2, Real.sqrt 3 / 2],
      ![1 / 2, Real.sqrt 3 / 2], ![3 / 2, Real.sqrt 3 / 2], ![0, Real.sqrt 3],
      ![-1, 0], ![3 / 2, -Real.sqrt 3 / 2], ![1 / 2, -Real.sqrt 3 / 2],
      ![-1 / 2, -Real.sqrt 3 / 2], ![-3 / 2, -Real.sqrt 3 / 2], ![0, -Real.sqrt 3]} := by
  rw [roots, g2_positive]
  ext vector
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
    neg_eq_iff_eq_neg]
  norm_num only [Matrix.neg_cons, Matrix.neg_empty, neg_neg, neg_zero, neg_div]
  tauto

set_option maxHeartbeats 2000000 in
/-- Normal reflections in the G roots preserve the twelve signed vectors. -/
theorem g2_reflection_mem (normal vector : RealPlane) (hnormal : normal ∈ g2.roots)
    (hvector : vector ∈ g2.roots) :
    vector - (2 * realBilinearForm vector normal /
      realBilinearForm normal normal) • normal ∈ g2.roots := by
  have hcube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    rw [pow_succ, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [g2_roots] at hnormal hvector ⊢
  rcases hnormal with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hvector with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm, Matrix.smul_cons, Matrix.sub_cons,
    div_mul_div_comm, Real.mul_self_sqrt] <;> ring_nf <;>
    norm_num [Real.sq_sqrt, hcube] <;> (try ring_nf) <;> norm_num <;>
    simp [← Matrix.zero_empty]

/-- Every signed G root has positive squared length. -/
theorem g2_norm_pos (vector : RealPlane) (hvector : vector ∈ g2.roots) :
    0 < realBilinearForm vector vector := by
  have hsquare : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [g2_roots] at hvector
  rcases hvector with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [realBilinearForm, div_mul_div_comm, hsquare]

end Schubert.Dihedral.RootLattice
