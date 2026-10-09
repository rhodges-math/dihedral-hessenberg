import DihedralHessenberg.Dihedral.ReflectionCosetFixedPoints
import TauCeti.RepresentationTheory.Induction.Permutation

/-! # Characters of the standard reflection-coset permutation representations -/

namespace Schubert.Dihedral

variable {n : ℕ} [NeZero n]

/-- The reflection-coset character is its fixed-coset count. -/
theorem _root_.Schubert.Dihedral.IndexedReflectionCosets.character (index : PositiveRootIndex n)
    (element : DihedralGroup n) :
    (rootReflectionCosetRepresentation index).character element =
      (Nat.card (MulAction.fixedBy (RootReflectionCosets index) element) : ℂ) := by
  exact TauCeti.char_ofMulAction ℂ (RootReflectionCosets index) element

/-- The reflection-coset permutation representation has dimension n. -/
theorem _root_.Schubert.Dihedral.IndexedReflectionCosets.character_one (index : PositiveRootIndex n)
  :
    (rootReflectionCosetRepresentation index).character 1 = (n : ℂ) := by
  rw [_root_.Schubert.Dihedral.IndexedReflectionCosets.character, card_fixedBy_one_reflectionCosets]

/-- Nonidentity rotations have zero character in the reflection-coset representation. -/
theorem _root_.Schubert.Dihedral.IndexedReflectionCosets.character_r (index : PositiveRootIndex n)
    (coordinate : ZMod n) (hne : coordinate ≠ 0) :
    (rootReflectionCosetRepresentation index).character (DihedralGroup.r coordinate) = 0 := by
  rw [_root_.Schubert.Dihedral.IndexedReflectionCosets.character,
    card_fixedBy_r_reflectionCosets index coordinate hne, Nat.cast_zero]

/-- For odd n, the reflection-coset permutation character is one on every reflection. -/
theorem _root_.Schubert.Dihedral.IndexedReflectionCosets.character_sr_odd (index : PositiveRootIndex
  n)
    (hodd : Odd n) (coordinate : ZMod n) :
    (rootReflectionCosetRepresentation index).character (DihedralGroup.sr coordinate) = 1 := by
  rw [_root_.Schubert.Dihedral.IndexedReflectionCosets.character,
    card_fixedBy_sr_reflectionCosets_of_odd index hodd coordinate, Nat.cast_one]

/-- For even n, its reflection character is two in the generator's class and zero otherwise. -/
theorem _root_.Schubert.Dihedral.IndexedReflectionCosets.character_sr_even (index :
  PositiveRootIndex n)
    (heven : Even n) (coordinate : ZMod n) :
    (rootReflectionCosetRepresentation index).character (DihedralGroup.sr coordinate) =
      if IsConj (DihedralGroup.sr coordinate) (rootReflection index) then 2 else 0 := by
  rw [_root_.Schubert.Dihedral.IndexedReflectionCosets.character,
    card_fixedBy_sr_reflectionCosets_of_even index heven coordinate]
  split_ifs <;> norm_num

end Schubert.Dihedral
