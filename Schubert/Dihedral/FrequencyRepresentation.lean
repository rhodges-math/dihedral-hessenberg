import Schubert.Dihedral.PlaneCharacter
import TauCeti.RepresentationTheory.FDRep

/-! # Frequency pullbacks of the planar dihedral representation

Scaling both dihedral normal-form coordinates gives a group endomorphism. Pulling
back the plane representation gives the standard two-dimensional frequency family.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Scale both rotation and reflection normal-form coordinates by a dihedral frequency. -/
def dihedralFrequencyHom (n : ℕ) (frequency : ZMod n) :
    DihedralGroup n →* DihedralGroup n where
  toFun := fun element => match element with
    | .r exponent => .r (frequency * exponent)
    | .sr exponent => .sr (frequency * exponent)
  map_one' := by change DihedralGroup.r (frequency * 0) = DihedralGroup.r 0; rw [mul_zero]
  map_mul' := by
    rintro (first | first) (second | second) <;>
      simp only [DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr] <;>
      simp [mul_add, mul_sub]

/-- The frequency homomorphism multiplies rotation coordinates. -/
theorem dihedralFrequencyHom_r (n : ℕ) (frequency exponent : ZMod n) :
    dihedralFrequencyHom n frequency (.r exponent) = .r (frequency * exponent) := rfl

/-- The frequency homomorphism multiplies reflection coordinates. -/
theorem dihedralFrequencyHom_sr (n : ℕ) (frequency exponent : ZMod n) :
    dihedralFrequencyHom n frequency (.sr exponent) = .sr (frequency * exponent) := rfl

/-- The planar dihedral representation pulled back along frequency scaling. -/
def frequencyRepresentation (n : ℕ) [NeZero n] (frequency : ZMod n) :
    Representation ℂ (DihedralGroup n) ComplexPlane :=
  (vectorRepresentation n).comp (dihedralFrequencyHom n frequency)

/-- The frequency representation as a standard finite-dimensional bundled representation. -/
def frequencyFDRep (n : ℕ) [NeZero n] (frequency : ZMod n) : FDRep ℂ (DihedralGroup n) :=
  FDRep.of (frequencyRepresentation n frequency)

/-- Frequency representations have the standard cosine character on rotations. -/
theorem frequencyRepresentation_character_r (n : ℕ) [NeZero n]
    (frequency exponent : ZMod n) :
    (frequencyRepresentation n frequency).character (.r exponent) =
      2 * (Real.cos (2 * Real.pi * (frequency * exponent).val / n) : ℂ) :=
  vectorRepresentation_character_r n (frequency * exponent)

/-- Frequency representations have zero character on reflections. -/
theorem frequencyRepresentation_character_sr (n : ℕ) [NeZero n]
    (frequency exponent : ZMod n) :
    (frequencyRepresentation n frequency).character (.sr exponent) = 0 :=
  vectorRepresentation_character_sr n (frequency * exponent)

/-- Bundling the frequency representation preserves its character. -/
theorem frequencyFDRep_character (n : ℕ) [NeZero n] (frequency : ZMod n)
    (element : DihedralGroup n) :
    (frequencyFDRep n frequency).character element =
      (frequencyRepresentation n frequency).character element :=
  congrFun (FDRep.character_of _) element

/-- Every frequency representation has complex dimension two. -/
theorem frequencyFDRep_finrank (n : ℕ) [NeZero n] (frequency : ZMod n) :
    Module.finrank ℂ (frequencyFDRep n frequency) = 2 := by
  change Module.finrank ℂ ComplexPlane = 2
  simp [ComplexPlane]

end Schubert.Dihedral
