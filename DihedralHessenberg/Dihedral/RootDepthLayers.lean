import DihedralHessenberg.Dihedral.RootDepth
import Mathlib.Tactic

/-! # Depth layers of the positive dihedral roots -/

namespace Schubert.Dihedral

private theorem depth_upper {n : ℕ} (hthree : 3 ≤ n) (index : Fin n) :
    (positiveRootEquiv n index).depth hthree ≤ index.val / 2 + 1 := by
  let : NeZero n := ⟨by omega⟩
  let quarter := index.val / 4
  have hindex := index.isLt
  have hquarter : quarter < n := by dsimp [quarter]; omega
  have hcast : (quarter : ZMod n).val = quarter := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hquarter]
  have hnext : ((quarter + 1 : ℕ) : ZMod n).val = quarter + 1 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by dsimp [quarter]; omega)]
  have hnegative (element : DihedralGroup n)
      (hinv : index ∈ rightInversions n hthree element) :
      (positiveRootEquiv n index).depth hthree ≤ length n hthree element :=
    (positiveRootEquiv n index).depth_le hthree element
      ((mem_rightInversionSet n hthree element index).mpr hinv).2
  have hrem : index.val % 4 = 0 ∨ index.val % 4 = 1 ∨
      index.val % 4 = 2 ∨ index.val % 4 = 3 := by omega
  rcases hrem with hrem | hrem | hrem | hrem
  · have hlength := length_sr_neg_of_twice_add_one_le n hthree quarter
      (by dsimp [quarter]; omega)
    apply le_trans (hnegative (.sr (-(quarter : ZMod n))) ?_)
    · rw [hlength]; dsimp [quarter]; omega
    rw [mem_rightInversions_sr_iff]
    have hangle : angularIndex index = 2 * quarter := by
      simp only [angularIndex, ite_eq_left (show index.val % 2 = 0 by omega)]
      dsimp [quarter]; omega
    rw [hangle]
    by_cases hzero : quarter = 0
    · simp [hzero]
    · have hne : (quarter : ZMod n) ≠ 0 := by
        intro heq
        have := congrArg ZMod.val heq
        simp only [hcast, ZMod.val_zero] at this
        exact hzero this
      let : NeZero (quarter : ZMod n) := ⟨hne⟩
      rw [ZMod.val_neg_of_ne_zero, hcast]
      left
      have heq : 2 * quarter + 2 * (n - quarter) = 2 * n := by omega
      rw [heq, Nat.mod_self]
  · have hlength := length_sr_add_one_of_twice_add_one_le n hthree quarter
      (by dsimp [quarter]; omega)
    apply le_trans (hnegative (.sr ((quarter : ZMod n) + 1)) ?_)
    · rw [hlength]; dsimp [quarter]; omega
    rw [mem_rightInversions_sr_iff]
    have hangle : angularIndex index = n - 1 - 2 * quarter := by
      simp only [angularIndex, ite_eq_right (show index.val % 2 ≠ 0 by omega)]
      dsimp [quarter]; omega
    have hsum : ((quarter : ZMod n) + 1).val = quarter + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using hnext
    rw [hangle, hsum]
    right
    have heq : n - 1 - 2 * quarter + 2 * (quarter + 1) = n + 1 := by
      dsimp [quarter]; omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlength := length_r_neg_of_twice_le n hthree (quarter + 1)
      (by dsimp [quarter]; omega)
    apply le_trans (hnegative (.r (-((quarter + 1 : ℕ) : ZMod n))) ?_)
    · rw [hlength]; dsimp [quarter]; omega
    rw [mem_rightInversions_r_iff]
    have hangle : angularIndex index = 2 * quarter + 1 := by
      simp only [angularIndex, ite_eq_left (show index.val % 2 = 0 by omega)]
      dsimp [quarter]; omega
    have hne : ((quarter + 1 : ℕ) : ZMod n) ≠ 0 := by
      intro heq
      have := congrArg ZMod.val heq
      simp only [hnext, ZMod.val_zero] at this
      omega
    let : NeZero ((quarter + 1 : ℕ) : ZMod n) := ⟨hne⟩
    rw [hangle, ZMod.val_neg_of_ne_zero, hnext]
    have heq : 2 * quarter + 1 + 2 * (n - (quarter + 1)) = 2 * n - 1 := by
      dsimp [quarter]; omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]
    omega
  · have hlength := length_r_of_twice_le n hthree (quarter + 1)
      (by dsimp [quarter]; omega)
    apply le_trans (hnegative (.r ((quarter + 1 : ℕ) : ZMod n)) ?_)
    · rw [hlength]; dsimp [quarter]; omega
    rw [mem_rightInversions_r_iff, hnext]
    have hangle : angularIndex index = n - 2 - 2 * quarter := by
      simp only [angularIndex, ite_eq_right (show index.val % 2 ≠ 0 by omega)]
      dsimp [quarter]; omega
    rw [hangle]
    have heq : n - 2 - 2 * quarter + 2 * (quarter + 1) = n := by
      dsimp [quarter]; omega
    rw [heq, Nat.mod_eq_of_lt (by omega)]

/-- Root depth is its alternating layer number, starting at one. -/
theorem PositiveRoot.depth_layer {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    alpha.depth hthree = alpha.index.val / 2 + 1 := by
  apply Nat.le_antisymm _ (alpha.layer_le_depth hthree)
  have h := depth_upper hthree alpha.index
  have hroot : positiveRootEquiv n alpha.index = alpha :=
    (positiveRootEquiv n).apply_symm_apply alpha
  rwa [hroot] at h

end Schubert.Dihedral
