import Schubert.Dihedral.Conjugacy
import Schubert.Dihedral.CommutingCoordinates
import Mathlib.GroupTheory.Coset.Basic

/-! # Exact counts of doubling fibers in finite cyclic coordinates -/

namespace Schubert.Dihedral

private theorem card_double_fiber_eq_kernel (n : ℕ) (target witness : ZMod n)
    (hwitness : 2 * witness = target) :
    Nat.card {coordinate : ZMod n // 2 * coordinate = target} =
      Nat.card {coordinate : ZMod n // 2 * coordinate = 0} := by
  let doubling : ZMod n →+ ZMod n :=
    { toFun := fun coordinate => 2 * coordinate
      map_zero' := mul_zero _
      map_add' := fun first second => mul_add _ first second }
  rw [← hwitness]
  exact Nat.card_congr (doubling.fiberEquivKer witness)

/-- For odd n, every doubling equation has exactly one cyclic-coordinate solution. -/
theorem card_double_fiber_of_odd (n : ℕ) (hodd : Odd n) (target : ZMod n) :
    Nat.card {coordinate : ZMod n // 2 * coordinate = target} = 1 := by
  have hcoprime : Nat.Coprime 2 n :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat
  let unit := ZMod.unitOfCoprime 2 hcoprime
  have hcoe : (unit : ZMod n) = 2 := ZMod.coe_unitOfCoprime 2 hcoprime
  have hwitness : 2 * ((unit⁻¹ : ZMod n) * target) = target := by
    rw [← hcoe]
    exact unit.mul_inv_cancel_left target
  rw [card_double_fiber_eq_kernel n target _ hwitness]
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨0, by simp⟩, ?_⟩
  intro coordinate
  apply Subtype.ext
  apply (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp
  simpa only [two_mul] using coordinate.property

/-- For even n, a doubling equation has two solutions for even target parity and none otherwise. -/
theorem card_double_fiber_of_even (n : ℕ) [NeZero n] (heven : Even n) (target : ZMod n) :
    Nat.card {coordinate : ZMod n // 2 * coordinate = target} =
      if target.val % 2 = 0 then 2 else 0 := by
  have hexists : (∃ coordinate : ZMod n, 2 * coordinate = target) ↔ target.val % 2 = 0 := by
    have heq := (isConj_sr_iff n 0 target).symm.trans
      (isConj_sr_iff_val_parity_of_even n heven 0 target)
    simpa only [sub_zero, ZMod.val_zero, Nat.zero_mod, eq_comm] using heq
  by_cases hparity : target.val % 2 = 0
  · rw [ite_eq_left hparity]
    obtain ⟨witness, hwitness⟩ := hexists.mpr hparity
    rw [card_double_fiber_eq_kernel n target witness hwitness]
    simpa only [two_mul] using card_add_self_eq_zero_of_even n heven
  · rw [ite_eq_right hparity]
    have hempty : IsEmpty {coordinate : ZMod n // 2 * coordinate = target} :=
      ⟨fun coordinate => hparity (hexists.mp ⟨coordinate.val, coordinate.property⟩)⟩
    let _ := hempty
    simp

end Schubert.Dihedral
