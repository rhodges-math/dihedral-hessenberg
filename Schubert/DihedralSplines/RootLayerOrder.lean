import Schubert.Dihedral.ConeCoordinates
import Schubert.DihedralSplines.HessenbergOrder
import Mathlib.Tactic.Abel

/-! # The real cone order in simple-root coordinates

The existing real-cone relation is coordinatewise comparison in the simple-root
basis. Its distinct roots compare exactly when their alternating layers compare.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- The real cone relation is coordinatewise comparison in the simple-root basis. -/
theorem rootLE_iff_coneCoordinates (n : ℕ) (hthree : 3 ≤ n)
    (first second : PositiveRootIndex n) :
    RootLE n hthree first second ↔
      rootConeCoordinates n first 0 ≤ rootConeCoordinates n second 0 ∧
        rootConeCoordinates n first 1 ≤ rootConeCoordinates n second 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, hcone⟩
    have hzero :
        (rootConeCoordinates n second 0 - rootConeCoordinates n first 0 - a) •
            positiveRoot n (firstSimpleRootIndex n hthree) +
          (rootConeCoordinates n second 1 - rootConeCoordinates n first 1 - b) •
            positiveRoot n (secondSimpleRootIndex n hthree) = 0 := by
      calc
        _ = (rootConeCoordinates n second 0 •
                positiveRoot n (firstSimpleRootIndex n hthree) +
              rootConeCoordinates n second 1 •
                positiveRoot n (secondSimpleRootIndex n hthree)) -
            (rootConeCoordinates n first 0 •
                positiveRoot n (firstSimpleRootIndex n hthree) +
              rootConeCoordinates n first 1 •
                positiveRoot n (secondSimpleRootIndex n hthree)) -
            (a • positiveRoot n (firstSimpleRootIndex n hthree) +
              b • positiveRoot n (secondSimpleRootIndex n hthree)) := by
              simp only [sub_smul]
              abel
        _ = 0 := by
          rw [← positiveRoot_eq_rootConeCoordinates n hthree second,
            ← positiveRoot_eq_rootConeCoordinates n hthree first, hcone, sub_self]
    obtain ⟨hfirst, hsecond⟩ := simpleRoot_coefficients_eq_zero n hthree _ _ hzero
    constructor <;> linarith
  · rintro ⟨hfirst, hsecond⟩
    refine ⟨rootConeCoordinates n second 0 - rootConeCoordinates n first 0,
      rootConeCoordinates n second 1 - rootConeCoordinates n first 1,
      sub_nonneg.mpr hfirst, sub_nonneg.mpr hsecond, ?_⟩
    rw [positiveRoot_eq_rootConeCoordinates n hthree second,
      positiveRoot_eq_rootConeCoordinates n hthree first]
    simp only [sub_smul]
    abel


/-- The lower of the two sine-ratio coefficients in a root layer. -/
private noncomputable def layerLower (n k : ℕ) : ℝ :=
  Real.sin ((k : ℝ) * (Real.pi / n)) / Real.sin (Real.pi / n)

/-- The upper of the two sine-ratio coefficients in a root layer. -/
private noncomputable def layerUpper (n k : ℕ) : ℝ :=
  Real.sin ((k : ℝ) * (Real.pi / n) + Real.pi / n) / Real.sin (Real.pi / n)

private theorem fundamentalAngle_pos (n : ℕ) (hthree : 3 ≤ n) :
    0 < Real.pi / n := div_pos Real.pi_pos (Nat.cast_pos.mpr (by omega))

private theorem fundamentalAngle_mul (n : ℕ) (hthree : 3 ≤ n) :
    (n : ℝ) * (Real.pi / n) = Real.pi := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp [hn]

private theorem layerMidpoint_le_half_pi (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2 ≤ Real.pi / 2 := by
  have hbound : (2 : ℝ) * (index.val / 2 : ℕ) + 1 ≤ n := by
    exact_mod_cast (show 2 * (index.val / 2) + 1 ≤ n by have := index.isLt; omega)
  have hmul := mul_le_mul_of_nonneg_right hbound (fundamentalAngle_pos n hthree).le
  rw [fundamentalAngle_mul n hthree] at hmul
  nlinarith

private theorem layerLower_le_upper (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    layerLower n (index.val / 2) ≤ layerUpper n (index.val / 2) := by
  apply (div_le_div_iff_of_pos_right (fundamentalAngle_sin_pos n hthree)).mpr
  rw [← sub_nonneg, Real.sin_sub_sin]
  have htheta := fundamentalAngle_pos n hthree
  have hmid := layerMidpoint_le_half_pi n hthree index
  have hk : (0 : ℝ) ≤ (index.val / 2 : ℕ) := Nat.cast_nonneg _
  have hsin : 0 ≤ Real.sin ((Real.pi / n) / 2) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [mul_nonneg hk htheta.le, Real.pi_pos]
  have hcos : 0 ≤ Real.cos
      (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · nlinarith [mul_nonneg hk htheta.le, Real.pi_pos]
    · exact hmid
  have hdiff :
      ((((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) -
        ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / 2 = (Real.pi / n) / 2 := by ring
  have hsum :
      ((((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) +
        ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / 2 =
        ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2 := by ring
  rw [hdiff, hsum]
  exact mul_nonneg (mul_nonneg (by norm_num) hsin) hcos

private theorem coneCoordinates_between_layer_bounds (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) (coordinate : Fin 2) :
    layerLower n (index.val / 2) ≤ rootConeCoordinates n index coordinate ∧
      rootConeCoordinates n index coordinate ≤ layerUpper n (index.val / 2) := by
  have horder := layerLower_le_upper n hthree index
  by_cases heven : index.val % 2 = 0
  · rw [rootConeCoordinates_of_even n index heven]
    fin_cases coordinate
    · exact ⟨horder, le_rfl⟩
    · exact ⟨le_rfl, horder⟩
  · rw [rootConeCoordinates_of_odd n hthree index heven]
    fin_cases coordinate
    · exact ⟨le_rfl, horder⟩
    · exact ⟨horder, le_rfl⟩

private theorem layerUpper_le_lower_of_lt (n : ℕ) (hthree : 3 ≤ n)
    (first second : PositiveRootIndex n) (hlt : first.val / 2 < second.val / 2) :
    layerUpper n (first.val / 2) ≤ layerLower n (second.val / 2) := by
  apply (div_le_div_iff_of_pos_right (fundamentalAngle_sin_pos n hthree)).mpr
  have htheta := fundamentalAngle_pos n hthree
  have hmid := layerMidpoint_le_half_pi n hthree second
  have hcast : ((first.val / 2 : ℕ) : ℝ) + 1 ≤ (second.val / 2 : ℕ) := by
    exact_mod_cast (show first.val / 2 + 1 ≤ second.val / 2 by omega)
  have hmul := mul_le_mul_of_nonneg_right hcast htheta.le
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · have hk : (0 : ℝ) ≤ (first.val / 2 : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hk htheta.le, Real.pi_pos]
  · nlinarith
  · nlinarith

private theorem coneCoordinates_sum (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    rootConeCoordinates n index 0 + rootConeCoordinates n index 1 =
      (2 * Real.cos ((Real.pi / n) / 2)) *
        Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2) /
          Real.sin (Real.pi / n) := by
  have htrig :
      Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) +
        Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) =
      (2 * Real.cos ((Real.pi / n) / 2)) *
        Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2) := by
    rw [Real.sin_add_sin]
    have havg :
        ((((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) +
          ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / 2 =
          ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + (Real.pi / n) / 2 := by ring
    have hdiff :
        ((((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) -
          ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / 2 = (Real.pi / n) / 2 := by ring
    rw [havg, hdiff]
    ring
  by_cases heven : index.val % 2 = 0
  · rw [rootConeCoordinates_of_even n index heven]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← add_div, htrig]
  · rw [rootConeCoordinates_of_odd n hthree index heven]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ← add_div]
    rw [add_comm, htrig]

private theorem coneCoordinates_sum_lt_of_layer_lt (n : ℕ) (hthree : 3 ≤ n)
    (first second : PositiveRootIndex n) (hlt : first.val / 2 < second.val / 2) :
    rootConeCoordinates n first 0 + rootConeCoordinates n first 1 <
      rootConeCoordinates n second 0 + rootConeCoordinates n second 1 := by
  rw [coneCoordinates_sum n hthree first, coneCoordinates_sum n hthree second]
  apply (div_lt_div_iff_of_pos_right (fundamentalAngle_sin_pos n hthree)).mpr
  have htheta := fundamentalAngle_pos n hthree
  have hmid := layerMidpoint_le_half_pi n hthree second
  have hthetaHalf : (Real.pi / n) / 2 < Real.pi / 2 := by
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hnlarge : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hsmall : Real.pi / n < Real.pi := by
      rw [div_lt_iff₀ hn]
      nlinarith [Real.pi_pos]
    linarith
  have hcos : 0 < Real.cos ((Real.pi / n) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hthetaHalf⟩
  apply mul_lt_mul_of_pos_left _ (mul_pos (by norm_num) hcos)
  apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
  · have hk : (0 : ℝ) ≤ (first.val / 2 : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg hk htheta.le, Real.pi_pos]
  · exact hmid
  · have hcast : ((first.val / 2 : ℕ) : ℝ) < (second.val / 2 : ℕ) := by
      exact_mod_cast hlt
    linarith [mul_lt_mul_of_pos_right hcast htheta]

/-- The real cone order compares distinct roots exactly by their alternating layers. -/
theorem rootLE_iff_eq_or_layer_lt (n : ℕ) (hthree : 3 ≤ n)
    (first second : PositiveRootIndex n) :
    RootLE n hthree first second ↔ first = second ∨ first.val / 2 < second.val / 2 := by
  constructor
  · intro hle
    obtain ⟨hfirst, hsecond⟩ := (rootLE_iff_coneCoordinates n hthree first second).mp hle
    rcases lt_trichotomy (first.val / 2) (second.val / 2) with hlt | heq | hgt
    · exact Or.inr hlt
    · have hsum : rootConeCoordinates n first 0 + rootConeCoordinates n first 1 =
          rootConeCoordinates n second 0 + rootConeCoordinates n second 1 := by
        rw [coneCoordinates_sum n hthree first, coneCoordinates_sum n hthree second, heq]
      have hzero : rootConeCoordinates n first 0 = rootConeCoordinates n second 0 := by
        linarith
      have hone : rootConeCoordinates n first 1 = rootConeCoordinates n second 1 := by
        linarith
      apply Or.inl
      apply positiveRoot_injective n
      rw [positiveRoot_eq_rootConeCoordinates n hthree first,
        positiveRoot_eq_rootConeCoordinates n hthree second, hzero, hone]
    · have hsum := coneCoordinates_sum_lt_of_layer_lt n hthree second first hgt
      linarith
  · rintro (rfl | hlt)
    · exact rootLE_refl n hthree first
    · apply (rootLE_iff_coneCoordinates n hthree first second).mpr
      have hmiddle := layerUpper_le_lower_of_lt n hthree first second hlt
      constructor
      · exact (coneCoordinates_between_layer_bounds n hthree first 0).2.trans
          (hmiddle.trans (coneCoordinates_between_layer_bounds n hthree second 0).1)
      · exact (coneCoordinates_between_layer_bounds n hthree first 1).2.trans
          (hmiddle.trans (coneCoordinates_between_layer_bounds n hthree second 1).1)

end Schubert.DihedralSplines
