import Mathlib.Tactic.Linarith
import Schubert.Dihedral.RootGeometry
import Schubert.DihedralSplines.HessenbergBasic

/-! # Antisymmetry of the real root relation

The nonnegative cone in the two linearly independent simple roots is pointed.
Combined with the injectivity of positive-root coordinates, this proves antisymmetry
of the root relation.
-/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Two positive roots that lie below one another in the simple-root cone are equal. -/
theorem rootLE_antisymm {n : ℕ} {hthree : 3 ≤ n} {first second : PositiveRootIndex n}
    (hforward : RootLE n hthree first second) (hbackward : RootLE n hthree second first) :
    first = second := by
  obtain ⟨a, b, ha, hb, hforward⟩ := hforward
  obtain ⟨c, d, hc, hd, hbackward⟩ := hbackward
  have hsum : (a + c) • positiveRoot n (firstSimpleRootIndex n hthree) +
      (b + d) • positiveRoot n (secondSimpleRootIndex n hthree) = 0 := by
    calc
      _ = (positiveRoot n second - positiveRoot n first) +
          (positiveRoot n first - positiveRoot n second) := by
        rw [hforward, hbackward]
        simp only [add_smul]
        abel
      _ = 0 := by abel
  obtain ⟨hfirstCoefficient, hsecondCoefficient⟩ :=
    simpleRoot_coefficients_eq_zero n hthree (a + c) (b + d) hsum
  have haZero : a = 0 := by linarith
  have hbZero : b = 0 := by linarith
  rw [haZero, hbZero, zero_smul, zero_smul, add_zero] at hforward
  exact positiveRoot_injective n (sub_eq_zero.mp hforward).symm

end Schubert.DihedralSplines
