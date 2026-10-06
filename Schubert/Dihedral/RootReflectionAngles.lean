import Schubert.Dihedral.RootSigns
import Schubert.Dihedral.ReflectionIndex

/-! # Angular coordinates of the indexed root reflections -/

namespace Schubert.Dihedral

/-- A positive root's reflection coordinate is the negative angular position modulo n. -/
theorem reflectionCoordinate_eq_neg_angularIndex {n : ℕ}
    (index : PositiveRootIndex n) :
    reflectionCoordinate index = -(angularIndex index : ZMod n) := by
  have hindex := index.isLt
  unfold reflectionCoordinate angularIndex
  split_ifs with heven
  · rfl
  · rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      ZMod.natCast_self, Nat.cast_one, Nat.cast_add, Nat.cast_one]
    ring

/-- The indexed root reflection has the negative angular position as its modular exponent. -/
theorem rootReflection_eq_sr_neg_angularIndex {n : ℕ} (index : PositiveRootIndex n) :
    rootReflection index = .sr (-(angularIndex index : ZMod n)) := by
  rw [rootReflection_eq_sr, reflectionCoordinate_eq_neg_angularIndex]

/-- Right multiplication by a root reflection converts rotation to reflection. -/
theorem r_mul_rootReflection {n : ℕ} (exponent : ZMod n) (index : PositiveRootIndex n) :
    DihedralGroup.r exponent * rootReflection index =
      .sr (-((angularIndex index : ZMod n) + exponent)) := by
  rw [rootReflection_eq_sr_neg_angularIndex, DihedralGroup.r_mul_sr]
  congr 1
  ring

/-- Right multiplication by a root reflection converts reflection to rotation. -/
theorem sr_mul_rootReflection {n : ℕ} (exponent : ZMod n) (index : PositiveRootIndex n) :
    DihedralGroup.sr exponent * rootReflection index =
      .r (-((angularIndex index : ZMod n) + exponent)) := by
  rw [rootReflection_eq_sr_neg_angularIndex, DihedralGroup.sr_mul_sr]
  congr 1
  ring

end Schubert.Dihedral
