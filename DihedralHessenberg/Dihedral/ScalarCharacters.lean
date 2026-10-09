import DihedralHessenberg.Dihedral.PlaneDeterminant
import TauCeti.RepresentationTheory.FDRep
import DihedralHessenberg.FiniteGroupCharacters.ScalarCharacter
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic.FinCases

/-! # One-dimensional dihedral character models

The determinant is the sign character. For even rotation order, reduction modulo two
supplies the two characters with rotation value minus one and chosen reflection sign.
-/

noncomputable section

open Schubert.FiniteGroupCharacters

namespace Schubert.Dihedral

/-- The dihedral determinant character on the plane representation. -/
def signCharacter (n : ℕ) [NeZero n] : DihedralGroup n →* ℂ :=
  LinearMap.det.comp (vectorRepresentation n)

/-- The sign character is one on every rotation. -/
theorem signCharacter_r (n : ℕ) [NeZero n] (exponent : ZMod n) :
    signCharacter n (.r exponent) = 1 := vectorRepresentation_det_r n exponent

/-- The sign character is minus one on every reflection. -/
theorem signCharacter_sr (n : ℕ) [NeZero n] (exponent : ZMod n) :
    signCharacter n (.sr exponent) = -1 := vectorRepresentation_det_sr n exponent

/-- The one-dimensional sign representation in the standard representation category. -/
def signRepresentation (n : ℕ) [NeZero n] : Representation ℂ (DihedralGroup n) ℂ :=
  ScalarCharacter.representation (signCharacter n)

/-- The finite-dimensional standard object for the sign representation. -/
def signFDRep (n : ℕ) [NeZero n] : FDRep ℂ (DihedralGroup n) := FDRep.of (signRepresentation n)

/-- Reduction of dihedral normal-form coordinates along the canonical quotient ring map. -/
def dihedralReductionHom (n m : ℕ) (hdivides : m ∣ n) :
    DihedralGroup n →* DihedralGroup m where
  toFun := fun element => match element with
    | .r exponent => .r (ZMod.castHom hdivides (ZMod m) exponent)
    | .sr exponent => .sr (ZMod.castHom hdivides (ZMod m) exponent)
  map_one' := by
    change DihedralGroup.r ((ZMod.castHom hdivides (ZMod m)) 0) = DihedralGroup.r 0
    rw [map_zero]
  map_mul' := by
    rintro (first | first) (second | second) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, map_add, map_sub]

private theorem zmod_two_eq_zero_or_one (value : ZMod 2) : value = 0 ∨ value = 1 := by
  have hval : value.val = 0 ∨ value.val = 1 := by
    have := value.val_lt
    omega
  rcases hval with hzero | hone
  · left
    apply ZMod.val_injective 2
    simpa using hzero
  · right
    apply ZMod.val_injective 2
    simpa [ZMod.val_one_eq_one_mod] using hone

/-- Either of the two scalar characters with rotation value minus one on the order-four group. -/
def dihedralTwoScalarCharacter (reflectionNegative : Bool) : DihedralGroup 2 →* ℂ where
  toFun := fun element => match element with
    | .r exponent => (-1 : ℂ) ^ exponent.val
    | .sr exponent => (if reflectionNegative then -1 else 1) * (-1 : ℂ) ^ exponent.val
  map_one' := by
    change (-1 : ℂ) ^ (0 : ZMod 2).val = 1
    norm_num
  map_mul' := by
    rintro (first | first) (second | second) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;>
      rcases zmod_two_eq_zero_or_one first with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one second with rfl | rfl <;>
      cases reflectionNegative <;>
      norm_num [ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod, ZMod.val_add,
        sub_eq_add_neg, ZMod.neg_val]
/-- The even-order character with rotation sign minus one and chosen first-reflection sign. -/
def evenScalarCharacter (n : ℕ) (heven : Even n) (reflectionNegative : Bool) :
    DihedralGroup n →* ℂ :=
  (dihedralTwoScalarCharacter reflectionNegative).comp
    (dihedralReductionHom n 2 (even_iff_two_dvd.mp heven))

/-- The corresponding standard one-dimensional even-order representation. -/
def evenScalarRepresentation (n : ℕ) (heven : Even n) (reflectionNegative : Bool) :
    Representation ℂ (DihedralGroup n) ℂ :=
  ScalarCharacter.representation (evenScalarCharacter n heven reflectionNegative)

/-- The finite-dimensional even-order scalar representation object. -/
def evenScalarFDRep (n : ℕ) (heven : Even n) (reflectionNegative : Bool) :
    FDRep ℂ (DihedralGroup n) := FDRep.of (evenScalarRepresentation n heven reflectionNegative)

/-- The even scalar character negates the fundamental rotation. -/
theorem evenScalarCharacter_rotation (n : ℕ) (heven : Even n)
    (reflectionNegative : Bool) :
    evenScalarCharacter n heven reflectionNegative (rotation n) = -1 := by
  rw [rotation_eq_r_one]
  change (-1 : ℂ) ^
    (ZMod.castHom (even_iff_two_dvd.mp heven) (ZMod 2) (1 : ZMod n)).val = -1
  rw [map_one]
  norm_num [ZMod.val_one_eq_one_mod]

/-- Its first simple-reflection value is the chosen sign. -/
theorem evenScalarCharacter_s1 (n : ℕ) (heven : Even n) (reflectionNegative : Bool) :
    evenScalarCharacter n heven reflectionNegative (firstSimpleReflection n) =
      if reflectionNegative then -1 else 1 := by
  simp [evenScalarCharacter, dihedralReductionHom, dihedralTwoScalarCharacter,
    firstSimpleReflection]

/-- The standard sign object has the determinant character. -/
theorem signFDRep_character (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    (signFDRep n).character element = signCharacter n element := by
  change (FDRep.of (ScalarCharacter.representation (signCharacter n))).character element = _
  rw [FDRep.character_of]
  exact ScalarCharacter.character _ _

/-- The standard even scalar object has its chosen scalar character. -/
theorem evenScalarFDRep_character (n : ℕ) (heven : Even n)
    (reflectionNegative : Bool) (element : DihedralGroup n) :
    (evenScalarFDRep n heven reflectionNegative).character element =
      evenScalarCharacter n heven reflectionNegative element := by
  change (FDRep.of (ScalarCharacter.representation
    (evenScalarCharacter n heven reflectionNegative))).character element = _
  rw [FDRep.character_of]
  exact ScalarCharacter.character _ _

end Schubert.Dihedral
