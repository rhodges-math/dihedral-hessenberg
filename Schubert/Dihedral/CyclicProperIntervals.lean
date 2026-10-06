import Schubert.Dihedral.CyclicIntervals

/-! # Initial positions of proper cyclic intervals -/

namespace Schubert.Dihedral.Cyclic

/-- Every nonempty proper interval determines its initial position. -/
theorem proper_interval_injective {n : ℕ} {hthree : 3 ≤ n} (size : ℕ)
    (hpositive : 0 < size) (hsize : size < 2 * n) :
    Function.Injective (fun start : Fin (2 * n) => interval n hthree start size) := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  intro first second heq
  change interval n hthree first size = interval n hthree second size at heq
  have hfirst : vertex n hthree first ∈ interval n hthree first size := by
    rw [mem_interval _ _ _ (by omega), sub_self, Fin.val_zero]
    exact hpositive
  have hprevious : vertex n hthree (first - 1) ∉ interval n hthree first size := by
    rw [mem_interval _ _ _ (by omega)]
    rw [show (first - 1) - first = -(1 : Fin (2 * n)) by abel]
    change ¬(2 * n - (1 % (2 * n))) % (2 * n) < size
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * n),
      Nat.mod_eq_of_lt (by omega : 2 * n - 1 < 2 * n)]
    omega
  rw [heq, mem_interval _ _ _ (by omega)] at hfirst hprevious
  rw [show (first - 1) - second = (first - second) - 1 by abel] at hprevious
  by_cases hzero : first - second = 0
  · exact sub_eq_zero.mp hzero
  · rw [Fin.val_sub_one_of_ne_zero hzero] at hprevious
    omega

end Schubert.Dihedral.Cyclic
