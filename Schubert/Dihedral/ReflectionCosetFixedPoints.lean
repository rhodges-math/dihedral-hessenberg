import Schubert.Dihedral.ReflectionCosetCoordinates
import Schubert.Dihedral.DoublingFibers

/-! # Fixed-point counts on the reflection cosets -/

namespace Schubert.Dihedral

variable {n : ℕ} [NeZero n]

/-- The identity fixes all n reflection cosets. -/
theorem card_fixedBy_one_reflectionCosets (index : PositiveRootIndex n) :
    Nat.card (MulAction.fixedBy (RootReflectionCosets index) (1 : DihedralGroup n)) = n := by
  change Nat.card {coset : RootReflectionCosets index //
    (1 : DihedralGroup n) • coset = coset} = n
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun coset => one_smul _ coset))]
  exact card_rootReflectionCosets index

/-- Every nonidentity rotation has no fixed reflection cosets. -/
theorem card_fixedBy_r_reflectionCosets (index : PositiveRootIndex n)
    (coordinate : ZMod n) (hne : coordinate ≠ 0) :
    Nat.card (MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.r coordinate)) = 0 := by
  have hempty : IsEmpty
      (MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.r coordinate)) := by
    constructor
    intro coset
    obtain ⟨rotation, hrotation⟩ := rotationCoset_surjective index coset.val
    have hfixed := coset.property
    rw [← hrotation] at hfixed
    exact hne ((r_smul_rotationCoset_eq_iff index coordinate rotation).mp hfixed)
  let _ := hempty
  simp

/-- Reflection-fixed cosets are counted by the associated doubling fiber. -/
theorem _root_.Schubert.Dihedral.ReflectionCosets.fixed_sr_card_fiber (index : PositiveRootIndex n)
    (coordinate : ZMod n) :
    Nat.card (MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.sr coordinate)) =
      Nat.card {rotation : ZMod n // 2 * rotation = reflectionCoordinate index - coordinate} := by
  let equivalence :
      {rotation : ZMod n // 2 * rotation = reflectionCoordinate index - coordinate} ≃
        MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.sr coordinate) :=
    Equiv.subtypeEquiv (rotationCosetEquiv index)
      (fun rotation => (sr_smul_rotationCoset_eq_iff index coordinate rotation).symm)
  exact (Nat.card_congr equivalence).symm

/-- For odd n, every reflection fixes exactly one reflection coset. -/
theorem card_fixedBy_sr_reflectionCosets_of_odd (index : PositiveRootIndex n)
    (hodd : Odd n) (coordinate : ZMod n) :
    Nat.card (MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.sr coordinate)) =
      1 := by
  rw [_root_.Schubert.Dihedral.ReflectionCosets.fixed_sr_card_fiber, card_double_fiber_of_odd n
    hodd]

/-- For even n, a reflection fixes two cosets exactly in the generator's conjugacy class. -/
theorem card_fixedBy_sr_reflectionCosets_of_even (index : PositiveRootIndex n)
    (heven : Even n) (coordinate : ZMod n) :
    Nat.card (MulAction.fixedBy (RootReflectionCosets index) (DihedralGroup.sr coordinate)) =
      if IsConj (DihedralGroup.sr coordinate) (rootReflection index) then 2 else 0 := by
  rw [_root_.Schubert.Dihedral.ReflectionCosets.fixed_sr_card_fiber, card_double_fiber_of_even n
    heven,
    rootReflection_eq_sr]
  have hparity := isConj_sr_iff_val_parity_of_even n heven 0
    (reflectionCoordinate index - coordinate)
  rw [isConj_sr_iff, sub_zero] at hparity
  have hconj := isConj_sr_iff n coordinate (reflectionCoordinate index)
  have hiff : (reflectionCoordinate index - coordinate).val % 2 = 0 ↔
      IsConj (DihedralGroup.sr coordinate) (DihedralGroup.sr (reflectionCoordinate index)) := by
    simpa only [ZMod.val_zero, Nat.zero_mod, eq_comm] using hparity.symm.trans hconj.symm
  simp only [hiff]

end Schubert.Dihedral
