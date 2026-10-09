import DihedralHessenberg.Dihedral.ScalarParity
import DihedralHessenberg.Dihedral.RootCosetObjects
import DihedralHessenberg.Dihedral.Conjugacy

/-! # Scalar characters fixed by a root reflection -/

noncomputable section

namespace Schubert.Dihedral.PositiveRoot

/-- The even scalar character which is trivial on the given root reflection. -/
def scalarCharacter {n : ℕ} (alpha : PositiveRoot n) (heven : Even n) :
    DihedralGroup n →* ℂ :=
  evenScalarCharacter n heven (decide ((reflectionCoordinate alpha.index).val % 2 = 1))

/-- The standard finite-dimensional object of the root's even scalar character. -/
def scalarFDRep {n : ℕ} (alpha : PositiveRoot n) (heven : Even n) :
    FDRep ℂ (DihedralGroup n) :=
  Schubert.Dihedral.evenScalarFDRep n heven
    (decide ((reflectionCoordinate alpha.index).val % 2 = 1))

/-- The chosen even scalar character fixes the generating root reflection. -/
theorem scalarCharacter_reflection {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (heven : Even n) : alpha.scalarCharacter heven alpha.reflection = 1 := by
  change evenScalarCharacter n heven
    (decide ((reflectionCoordinate alpha.index).val % 2 = 1)) (rootReflection alpha.index) = 1
  rw [rootReflection_eq_sr, evenScalarCharacter_sr]
  have hbound : (reflectionCoordinate alpha.index).val % 2 < 2 := Nat.mod_lt _ (by decide)
  have hcases : (reflectionCoordinate alpha.index).val % 2 = 0 ∨
      (reflectionCoordinate alpha.index).val % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · simp [hzero]
  · simp [hone]

/-- The chosen even scalar character distinguishes the generator's reflection class. -/
theorem scalarCharacter_sr {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (heven : Even n) (coordinate : ZMod n) :
    alpha.scalarCharacter heven (.sr coordinate) =
      if IsConj (DihedralGroup.sr coordinate) alpha.reflection then 1 else -1 := by
  change evenScalarCharacter n heven
    (decide ((reflectionCoordinate alpha.index).val % 2 = 1)) (.sr coordinate) =
      if IsConj (DihedralGroup.sr coordinate) (rootReflection alpha.index) then 1 else -1
  simp only [rootReflection_eq_sr, isConj_sr_iff_val_parity_of_even n heven,
    evenScalarCharacter_sr]
  have halpha : (reflectionCoordinate alpha.index).val % 2 = 0 ∨
      (reflectionCoordinate alpha.index).val % 2 = 1 := by omega
  have hcoordinate : coordinate.val % 2 = 0 ∨ coordinate.val % 2 = 1 := by omega
  rcases halpha with hzero | hone
  · rcases hcoordinate with hzero' | hone'
    · simp [hzero, hzero']
    · simp [hzero, hone']
  · rcases hcoordinate with hzero' | hone'
    · simp [hone, hzero']
    · simp [hone, hone']

/-- Among the two even scalar characters, exactly the chosen one fixes the root reflection. -/
theorem scalarCharacter_unique {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (heven : Even n) (reflectionNegative : Bool) :
    evenScalarCharacter n heven reflectionNegative alpha.reflection = 1 ↔
      evenScalarCharacter n heven reflectionNegative = alpha.scalarCharacter heven := by
  constructor
  · intro hfixed
    change evenScalarCharacter n heven reflectionNegative (rootReflection alpha.index) = 1
      at hfixed
    rw [rootReflection_eq_sr, evenScalarCharacter_sr] at hfixed
    have hparity : (reflectionCoordinate alpha.index).val % 2 = 0 ∨
        (reflectionCoordinate alpha.index).val % 2 = 1 := by omega
    have hchoice : reflectionNegative =
        decide ((reflectionCoordinate alpha.index).val % 2 = 1) := by
      rcases hparity with hparity | hparity
      all_goals cases reflectionNegative
      all_goals norm_num [hparity] at hfixed
      all_goals simp [hparity]
    simp only [scalarCharacter]
    rw [hchoice]
  · intro hequal
    rw [hequal]
    exact alpha.scalarCharacter_reflection heven

end Schubert.Dihedral.PositiveRoot
