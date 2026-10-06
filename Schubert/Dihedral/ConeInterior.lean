import Schubert.Dihedral.RootSeparator

/-! # Simple-root coordinate bounds in the interior of the positive half-plane -/

namespace Schubert.Dihedral

private theorem sine_interval (theta angle : ℝ) (htheta : 0 ≤ theta)
    (hlower : theta ≤ angle) (hupper : angle ≤ Real.pi - theta) :
    Real.sin theta ≤ Real.sin angle := by
  by_cases hhalf : angle ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hhalf hlower
  · rw [← Real.sin_pi_sub angle]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith) (by linarith)

/-- Every non-simple positive root has both simple-root coordinates at least one. -/
theorem coneCoordinates_interior (n : ℕ) (hthree : 3 ≤ n) (alpha : PositiveRoot n)
    (hfirst : alpha ≠ simpleRoot n hthree 0) (hsecond : alpha ≠ simpleRoot n hthree 1)
    (coordinate : Fin 2) : 1 ≤ rootConeCoordinates n alpha.index coordinate := by
  have hindex : 2 ≤ alpha.index.val := by
    have hzero : alpha.index.val ≠ 0 := by
      intro heq
      apply hfirst
      apply (positiveRootEquiv n).symm.injective
      rw [simpleRoot_zero]
      apply Fin.ext
      rw [Equiv.symm_apply_apply]
      exact heq
    have hone : alpha.index.val ≠ 1 := by
      intro heq
      apply hsecond
      apply (positiveRootEquiv n).symm.injective
      rw [simpleRoot_one]
      apply Fin.ext
      rw [Equiv.symm_apply_apply]
      exact heq
    omega
  have hangular : 1 ≤ angularIndex alpha.index ∧ angularIndex alpha.index + 2 ≤ n := by
    have hlt := alpha.index.isLt
    unfold angularIndex
    split_ifs <;> omega
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have htheta : 0 ≤ Real.pi / n := (div_pos Real.pi_pos hn).le
  have hmul : (n : ℝ) * (Real.pi / n) = Real.pi := by
    field_simp [hn.ne']
  have hangle : rootAngle n alpha.index = (angularIndex alpha.index : ℝ) * (Real.pi / n) := by
    rw [rootAngle_eq_angularIndex]
    ring
  have hlower : Real.pi / n ≤ rootAngle n alpha.index := by
    rw [hangle]
    have hbound : (1 : ℝ) ≤ angularIndex alpha.index := by exact_mod_cast hangular.1
    nlinarith [mul_le_mul_of_nonneg_right hbound htheta]
  have hupper : rootAngle n alpha.index + 2 * (Real.pi / n) ≤ Real.pi := by
    rw [hangle]
    have hbound : (angularIndex alpha.index : ℝ) + 2 ≤ n := by exact_mod_cast hangular.2
    nlinarith [mul_le_mul_of_nonneg_right hbound htheta]
  have hden := fundamentalAngle_sin_pos n hthree
  fin_cases coordinate
  · change 1 ≤ Real.sin (rootAngle n alpha.index + Real.pi / n) / Real.sin (Real.pi / n)
    apply (le_div_iff₀ hden).mpr
    simpa only [one_mul] using sine_interval (Real.pi / n)
      (rootAngle n alpha.index + Real.pi / n) htheta (by linarith) (by linarith)
  · change 1 ≤ Real.sin (rootAngle n alpha.index) / Real.sin (Real.pi / n)
    apply (le_div_iff₀ hden).mpr
    simpa only [one_mul] using sine_interval (Real.pi / n)
      (rootAngle n alpha.index) htheta hlower (by linarith)

end Schubert.Dihedral
