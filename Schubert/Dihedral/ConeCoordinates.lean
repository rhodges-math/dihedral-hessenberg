import Schubert.Dihedral.RootGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Simple-root coordinates of positive dihedral roots

The cone coordinates of each positive unit root are sine ratios. This file uses
the real reflection representation.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The coefficients of a positive root in the ordered pair of simple roots. -/
def rootConeCoordinates (n : ℕ) (index : PositiveRootIndex n) : RealPlane :=
  ![Real.sin (rootAngle n index + Real.pi / n) / Real.sin (Real.pi / n),
    Real.sin (rootAngle n index) / Real.sin (Real.pi / n)]

/-- The sine of the fundamental angle is positive for a polygon with at least three sides. -/
theorem fundamentalAngle_sin_pos (n : ℕ) (hthree : 3 ≤ n) :
    0 < Real.sin (Real.pi / n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hlarge : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos hn
  · rw [div_lt_iff₀ hn]
    nlinarith [Real.pi_pos]

/-- The second simple root is at angle pi minus the fundamental angle. -/
theorem secondSimpleRoot_eq_unitRootAt (n : ℕ) (hthree : 3 ≤ n) :
    positiveRoot n (secondSimpleRootIndex n hthree) =
      unitRootAt (Real.pi - Real.pi / n) := by
  rw [positiveRoot, rootAngle_second]
  congr 1
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  field_simp [hn]

/-- The sine ratios reconstruct a positive root as a combination of the simple roots. -/
theorem positiveRoot_eq_rootConeCoordinates (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) :
    positiveRoot n index =
      rootConeCoordinates n index 0 • positiveRoot n (firstSimpleRootIndex n hthree) +
        rootConeCoordinates n index 1 • positiveRoot n (secondSimpleRootIndex n hthree) := by
  have hfirst : positiveRoot n (firstSimpleRootIndex n hthree) = unitRootAt 0 := by
    rw [positiveRoot, rootAngle_first]
  have hsin := (fundamentalAngle_sin_pos n hthree).ne'
  rw [hfirst, secondSimpleRoot_eq_unitRootAt]
  apply realPlane_ext
  · simp only [positiveRoot, unitRootAt, rootConeCoordinates, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.cos_zero, Real.cos_pi_sub, Real.sin_add, mul_one]
    field_simp [hsin]
    ring
  · simp only [positiveRoot, unitRootAt, rootConeCoordinates, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.sin_zero, Real.sin_pi_sub, mul_zero, zero_add]
    exact (div_mul_cancel₀ _ hsin).symm

/-- Even-indexed roots have the unswapped sine-ratio coefficients. -/
theorem rootConeCoordinates_of_even (n : ℕ) (index : PositiveRootIndex n)
    (heven : index.val % 2 = 0) :
    rootConeCoordinates n index =
      ![Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) /
          Real.sin (Real.pi / n),
        Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / Real.sin (Real.pi / n)] := by
  have hangle : rootAngle n index = ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) := by
    rw [rootAngle, ite_eq_left heven]
    ring
  simp only [rootConeCoordinates, hangle]

/-- Odd-indexed roots have the swapped sine-ratio coefficients. -/
theorem rootConeCoordinates_of_odd (n : ℕ) (hthree : 3 ≤ n) (index : PositiveRootIndex n)
    (hodd : index.val % 2 ≠ 0) :
    rootConeCoordinates n index =
      ![Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n)) / Real.sin (Real.pi / n),
        Real.sin (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) /
          Real.sin (Real.pi / n)] := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hangle : rootAngle n index =
      Real.pi - (((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) + Real.pi / n) := by
    rw [rootAngle, ite_eq_right hodd, Nat.cast_sub (by omega : index.val / 2 ≤ n - 1),
      Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp [hn]
    ring
  have hshift : rootAngle n index + Real.pi / n =
      Real.pi - ((index.val / 2 : ℕ) : ℝ) * (Real.pi / n) := by rw [hangle]; ring
  unfold rootConeCoordinates
  rw [hshift, hangle, Real.sin_pi_sub, Real.sin_pi_sub]

/-- A positive root plus one fundamental angle does not exceed pi. -/
theorem rootAngle_add_fundamental_le_pi (n : ℕ) (index : PositiveRootIndex n) :
    rootAngle n index + Real.pi / n ≤ Real.pi := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by have := index.isLt; omega)
  have hindex : ((angularIndex index : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (show angularIndex index + 1 ≤ n by have := angularIndex_lt index; omega)
  rw [rootAngle_eq_angularIndex]
  rw [← add_div, div_le_iff₀ hn]
  nlinarith [Real.pi_pos]

/-- Both simple-root coordinates of a positive root are nonnegative. -/
theorem rootConeCoordinates_nonneg (n : ℕ) (hthree : 3 ≤ n)
    (index : PositiveRootIndex n) (coordinate : Fin 2) :
    0 ≤ rootConeCoordinates n index coordinate := by
  have hden := (fundamentalAngle_sin_pos n hthree).le
  fin_cases coordinate
  · apply div_nonneg _ hden
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact add_nonneg (rootAngle_nonneg n index) (by positivity)
    · exact rootAngle_add_fundamental_le_pi n index
  · exact div_nonneg (positiveRoot_second_coordinate_nonneg n index) hden

end Schubert.Dihedral
