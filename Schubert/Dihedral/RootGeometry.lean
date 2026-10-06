import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Schubert.Dihedral.RealizationBasic

/-! # Angular coordinates of positive dihedral roots

The alternating root numbering permutes the angular positions from zero to `n - 1`.
Consequently the positive unit roots are distinct and lie in the upper half-plane.
The two simple roots are linearly independent over the reals.
-/

namespace Schubert.Dihedral

/-- The position of a positive root in the increasing angular ordering. -/
def angularIndex {n : ℕ} (index : PositiveRootIndex n) : ℕ :=
  if index.val % 2 = 0 then index.val / 2 else n - 1 - index.val / 2

theorem angularIndex_lt {n : ℕ} (index : PositiveRootIndex n) : angularIndex index < n := by
  have hindex := index.isLt
  unfold angularIndex
  split_ifs <;> omega

/-- Angular positions distinguish the alternating positive-root indices. -/
theorem angularIndex_injective (n : ℕ) : Function.Injective (angularIndex (n := n)) := by
  intro first second heq
  have hfirst := first.isLt
  have hsecond := second.isLt
  apply Fin.ext
  unfold angularIndex at heq
  split_ifs at heq <;> omega

/-- The root angle is its angular position times the fundamental angle. -/
theorem rootAngle_eq_angularIndex (n : ℕ) (index : PositiveRootIndex n) :
    rootAngle n index = angularIndex index * Real.pi / n := by
  unfold rootAngle angularIndex
  split_ifs <;> rfl

theorem rootAngle_nonneg (n : ℕ) (index : PositiveRootIndex n) : 0 ≤ rootAngle n index := by
  rw [rootAngle_eq_angularIndex]
  positivity

theorem rootAngle_lt_pi (n : ℕ) (index : PositiveRootIndex n) : rootAngle n index < Real.pi := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) index.isLt
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [rootAngle_eq_angularIndex, div_lt_iff₀ hnreal, mul_comm Real.pi]
  exact mul_lt_mul_of_pos_right (Nat.cast_lt.mpr (angularIndex_lt index)) Real.pi_pos

/-- Equality of angles implies equality of positive-root indices. -/
theorem rootAngle_injective (n : ℕ) : Function.Injective (rootAngle n) := by
  intro first second heq
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) first.isLt
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  apply angularIndex_injective n
  rw [rootAngle_eq_angularIndex, rootAngle_eq_angularIndex, div_left_inj' hnreal,
    mul_left_inj' Real.pi_ne_zero] at heq
  exact_mod_cast heq

/-- The indexed real positive roots are pairwise distinct. -/
theorem positiveRoot_injective (n : ℕ) : Function.Injective (positiveRoot n) := by
  intro first second heq
  apply rootAngle_injective n
  apply Real.injOn_cos
    ⟨rootAngle_nonneg n first, (rootAngle_lt_pi n first).le⟩
    ⟨rootAngle_nonneg n second, (rootAngle_lt_pi n second).le⟩
  have hcoordinate := congrFun heq 0
  simpa only [positiveRoot, unitRootAt, Matrix.cons_val_zero] using hcoordinate

/-- A positive unit root is nonzero. -/
theorem positiveRoot_ne_zero (n : ℕ) (index : PositiveRootIndex n) :
    positiveRoot n index ≠ 0 := by
  intro hzero
  have hunit := positiveRoot_unit n index
  rw [hzero] at hunit
  simp [realBilinearForm] at hunit

/-- Positive roots have nonnegative second coordinate. -/
theorem positiveRoot_second_coordinate_nonneg (n : ℕ) (index : PositiveRootIndex n) :
    0 ≤ positiveRoot n index 1 :=
  Real.sin_nonneg_of_nonneg_of_le_pi (rootAngle_nonneg n index) (rootAngle_lt_pi n index).le

/-- A positive root on the first coordinate axis has angle zero. -/
theorem _root_.Schubert.Dihedral.IndexedRoots.angle_zero_of_y_zero (n : ℕ) (index :
  PositiveRootIndex n)
    (hzero : positiveRoot n index 1 = 0) : rootAngle n index = 0 := by
  rcases lt_or_eq_of_le (rootAngle_nonneg n index) with hpositive | hzeroAngle
  · have hsin := Real.sin_pos_of_pos_of_lt_pi hpositive (rootAngle_lt_pi n index)
    change Real.sin (rootAngle n index) = 0 at hzero
    exact False.elim (hsin.ne' hzero)
  · exact hzeroAngle.symm

/-- The positive root set contains no opposite pair. -/
theorem positiveRoot_ne_neg (n : ℕ) (first second : PositiveRootIndex n) :
    positiveRoot n first ≠ -positiveRoot n second := by
  intro heq
  have hsecondCoordinates := congrFun heq 1
  change positiveRoot n first 1 = -positiveRoot n second 1 at hsecondCoordinates
  have hfirstNonnegative := positiveRoot_second_coordinate_nonneg n first
  have hsecondNonnegative := positiveRoot_second_coordinate_nonneg n second
  have hfirstZero : positiveRoot n first 1 = 0 := by linarith
  have hsecondZero : positiveRoot n second 1 = 0 := by linarith
  have hfirstAngle := _root_.Schubert.Dihedral.IndexedRoots.angle_zero_of_y_zero n first hfirstZero
  have hsecondAngle := _root_.Schubert.Dihedral.IndexedRoots.angle_zero_of_y_zero n second
    hsecondZero
  have hfirstCoordinates := congrFun heq 0
  change Real.cos (rootAngle n first) = -Real.cos (rootAngle n second) at hfirstCoordinates
  rw [hfirstAngle, hsecondAngle, Real.cos_zero] at hfirstCoordinates
  linarith

theorem rootAngle_first (n : ℕ) (hthree : 3 ≤ n) :
    rootAngle n (firstSimpleRootIndex n hthree) = 0 := by
  simp [rootAngle, firstSimpleRootIndex]

theorem rootAngle_second (n : ℕ) (hthree : 3 ≤ n) :
    rootAngle n (secondSimpleRootIndex n hthree) = (n - 1 : ℕ) * Real.pi / n := by
  simp [rootAngle, secondSimpleRootIndex]

/-- The second simple root lies strictly above the first coordinate axis. -/
theorem secondSimpleRoot_second_coordinate_pos (n : ℕ) (hthree : 3 ≤ n) :
    0 < positiveRoot n (secondSimpleRootIndex n hthree) 1 := by
  change 0 < Real.sin (rootAngle n (secondSimpleRootIndex n hthree))
  apply Real.sin_pos_of_pos_of_lt_pi
  · rw [rootAngle_second]
    have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 3) hthree
    have hpred : 0 < n - 1 := by omega
    exact div_pos (mul_pos (Nat.cast_pos.mpr hpred) Real.pi_pos) (Nat.cast_pos.mpr hn)
  · exact rootAngle_lt_pi n _

/-- A vanishing linear combination of the two simple roots has zero coefficients. -/
theorem simpleRoot_coefficients_eq_zero (n : ℕ) (hthree : 3 ≤ n) (first second : ℝ)
    (hcombination : first • positiveRoot n (firstSimpleRootIndex n hthree) +
      second • positiveRoot n (secondSimpleRootIndex n hthree) = 0) :
    first = 0 ∧ second = 0 := by
  have hfirstRoot : positiveRoot n (firstSimpleRootIndex n hthree) = ![(1 : ℝ), 0] := by
    rw [positiveRoot, rootAngle_first]
    simp only [unitRootAt, Real.cos_zero, Real.sin_zero]
  have hsecondCoordinate := congrFun hcombination 1
  rw [hfirstRoot] at hsecondCoordinate
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_zero, zero_add, Pi.zero_apply] at hsecondCoordinate
  have hsecond : second = 0 := (mul_eq_zero.mp hsecondCoordinate).resolve_right
    (secondSimpleRoot_second_coordinate_pos n hthree).ne'
  have hfirstCoordinate := congrFun hcombination 0
  rw [hfirstRoot, hsecond] at hfirstCoordinate
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    mul_one, zero_mul, add_zero, Pi.zero_apply] at hfirstCoordinate
  exact ⟨hfirstCoordinate, hsecond⟩

end Schubert.Dihedral
