import Schubert.Dihedral.FrequencyFourier
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Integer-power characters and the defining frequency representation -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.Frequency

/-- The cyclic additive pair at an integer lift has the unreduced cosine formula. -/
theorem additive_pair_int (n : ℕ) [NeZero n] (coordinate : ℤ) :
    ZMod.stdAddChar (N := n) coordinate + ZMod.stdAddChar (-(coordinate : ZMod n)) =
      2 * (Real.cos (2 * Real.pi * coordinate / n) : ℂ) := by
  have hpositive := ZMod.stdAddChar_coe (N := n) coordinate
  have hnegative := ZMod.stdAddChar_coe (N := n) (-coordinate)
  simp only [Int.cast_neg] at hnegative
  rw [hpositive, hnegative, Complex.ofReal_cos, Complex.cos]
  push_cast
  have hfirst : 2 * (Real.pi : ℂ) * Complex.I * coordinate / n =
      (2 * (Real.pi : ℂ) * coordinate / n) * Complex.I := by ring
  have hsecond : 2 * (Real.pi : ℂ) * Complex.I * -(coordinate : ℂ) / n =
      -(2 * (Real.pi : ℂ) * coordinate / n) * Complex.I := by ring
  rw [hfirst, hsecond]
  ring

/-- Every integer power of the fundamental rotation has the exact frequency cosine trace. -/
theorem character_zpow (n : ℕ) [NeZero n] (frequency : ℕ) (exponent : ℤ) :
    (frequencyFDRep n frequency).character (rotation n ^ exponent) =
      2 * (Real.cos (2 * Real.pi * frequency * exponent / n) : ℂ) := by
  rw [rotation_eq_r_one, DihedralGroup.r_one_zpow, character_additive]
  have hproduct : ((frequency : ℕ) : ZMod n) * (exponent : ZMod n) =
      (((frequency : ℤ) * exponent : ℤ) : ZMod n) := by simp
  rw [hproduct, additive_pair_int]
  push_cast
  congr 2
  ring

/-- An integer rotation power followed by the first simple reflection has zero trace. -/
theorem character_zpow_s1 (n : ℕ) [NeZero n] (frequency : ZMod n) (exponent : ℤ) :
    (frequencyFDRep n frequency).character
      (rotation n ^ exponent * firstSimpleReflection n) = 0 := by
  have hreflection : rotation n ^ exponent * firstSimpleReflection n =
      DihedralGroup.sr (-(exponent : ZMod n)) := by
    rw [rotation_eq_r_one, DihedralGroup.r_one_zpow, firstSimpleReflection,
      DihedralGroup.r_mul_sr, zero_sub]
  rw [hreflection, frequencyFDRep_character, frequencyRepresentation_character_sr]

end Schubert.Dihedral.Frequency

namespace Schubert.Dihedral

/-- Frequency one is exactly the complex plane representation. -/
theorem frequency_one (n : ℕ) [NeZero n] :
    frequencyRepresentation n 1 = vectorRepresentation n := by
  apply MonoidHom.ext
  intro element
  change vectorRepresentation n (dihedralFrequencyHom n 1 element) = _
  cases element <;> simp [dihedralFrequencyHom]

/-- The first frequency object is the defining representation object. -/
theorem frequency_one_iso (n : ℕ) [NeZero n] :
    Nonempty (frequencyFDRep n 1 ≅ FDRep.of (vectorRepresentation n)) := by
  rw [frequencyFDRep, frequency_one]
  exact ⟨Iso.refl _⟩

end Schubert.Dihedral
