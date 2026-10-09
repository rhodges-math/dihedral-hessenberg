import DihedralHessenberg.Dihedral.RootAxioms
import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.ConeCoordinates

/-! # A separating hyperplane for signed dihedral roots -/

namespace Schubert.Dihedral

private theorem simple_pairing (n : ℕ) (hthree : 3 ≤ n) :
    realBilinearForm (simpleRoot n hthree 0).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
      1 - Real.cos (Real.pi / n) ∧
    realBilinearForm (simpleRoot n hthree 1).val
        ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
      1 - Real.cos (Real.pi / n) := by
  have hfirst : (simpleRoot n hthree 0).val = unitRootAt 0 := by
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
  have hsecond : (simpleRoot n hthree 1).val = unitRootAt (Real.pi - Real.pi / n) := by
    rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
  rw [hfirst, hsecond]
  simp only [realBilinearForm, unitRootAt, Pi.add_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.cos_zero, Real.sin_zero, Real.cos_pi_sub, Real.sin_pi_sub]
  constructor
  · ring
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi / n)]

/-- Every positive root is strictly on the simple-root bisector side of its hyperplane. -/
theorem PositiveRoot.halfspace_pos {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    0 < realBilinearForm alpha.val
      ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) := by
  let a := rootConeCoordinates n alpha.index 0
  let b := rootConeCoordinates n alpha.index 1
  have ha : 0 ≤ a := rootConeCoordinates_nonneg n hthree alpha.index 0
  have hb : 0 ≤ b := rootConeCoordinates_nonneg n hthree alpha.index 1
  have hexpansion : alpha.val =
      a • (simpleRoot n hthree 0).val + b • (simpleRoot n hthree 1).val := by
    rw [simpleRoot_zero, simpleRoot_one, positiveRootEquiv_val, positiveRootEquiv_val,
      ← positiveRoot_eq_rootConeCoordinates n hthree alpha.index, PositiveRoot.index_val]
  have hsum : 0 < a + b := by
    by_contra hnot
    have hzeroa : a = 0 := by linarith
    have hzerob : b = 0 := by linarith
    have hzero : alpha.val = 0 := by simpa only [hzeroa, hzerob, zero_smul, add_zero] using
      hexpansion
    have hunit := roots_unit alpha.val (Or.inl alpha.property)
    rw [hzero] at hunit
    norm_num [realBilinearForm] at hunit
  have hfactor : 0 < 1 - Real.cos (Real.pi / n) := by
    have hsin := fundamentalAngle_sin_pos n hthree
    have hcos := Real.cos_le_one (Real.pi / n)
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / n)]
  have hlinear : realBilinearForm alpha.val
      ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val) =
        (a + b) * (1 - Real.cos (Real.pi / n)) := by
    rw [hexpansion]
    have hdistrib (first second : RealPlane) :
        realBilinearForm (a • first + b • second) (first + second) =
          a * realBilinearForm first (first + second) +
            b * realBilinearForm second (first + second) := by
      simp only [realBilinearForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hdistrib, (simple_pairing n hthree).1, (simple_pairing n hthree).2]
    ring
  rw [hlinear]
  exact mul_pos hsum hfactor

/-- The positive roots are precisely the signed roots on one side of a generic hyperplane. -/
theorem positiveRoots_halfspace (n : ℕ) (hthree : 3 ≤ n) :
    positiveRoots n = {vector ∈ roots n | 0 < realBilinearForm vector
      ((simpleRoot n hthree 0).val + (simpleRoot n hthree 1).val)} := by
  ext vector
  constructor
  · intro hpositive
    exact ⟨Or.inl hpositive, PositiveRoot.halfspace_pos hthree ⟨vector, hpositive⟩⟩
  · rintro ⟨hroot, hpairing⟩
    rcases hroot with hpositive | hnegative
    · exact hpositive
    · have hnegative_pos := PositiveRoot.halfspace_pos hthree ⟨-vector, hnegative⟩
      simp only [realBilinearForm, Pi.neg_apply, neg_mul] at hpairing hnegative_pos
      linarith

/-- The separating hyperplane contains no signed root. -/
theorem roots_halfspace_nonzero (n : ℕ) (hthree : 3 ≤ n) (vector : RealPlane)
    (hroot : vector ∈ roots n) :
    realBilinearForm vector ((simpleRoot n hthree 0).val +
      (simpleRoot n hthree 1).val) ≠ 0 := by
  rcases hroot with hpositive | hnegative
  · exact ne_of_gt (PositiveRoot.halfspace_pos hthree ⟨vector, hpositive⟩)
  · have hpos := PositiveRoot.halfspace_pos hthree ⟨-vector, hnegative⟩
    simp only [realBilinearForm, Pi.neg_apply, neg_mul] at hpos ⊢
    linarith

end Schubert.Dihedral
