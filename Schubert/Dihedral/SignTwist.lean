import Schubert.Dihedral.ScalarParity
import Schubert.Dihedral.FrequencyRepresentation
import Schubert.Dihedral.FrequencySum
import TauCeti.RepresentationTheory.RepresentationRing.Injective

/-! # Sign twists of dihedral representations -/

noncomputable section

open CategoryTheory MonoidalCategory

namespace Schubert.Dihedral

/-- Tensoring a frequency representation with determinant sign preserves its isomorphism class. -/
theorem sign_frequency_iso (n : ℕ) [NeZero n] (frequency : ZMod n) :
    Nonempty ((signFDRep n ⊗ frequencyFDRep n frequency) ≅ frequencyFDRep n frequency) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_tensor, Pi.mul_apply, signFDRep_character]
  cases element with
  | r coordinate => rw [signCharacter_r, one_mul]
  | sr coordinate =>
      rw [signCharacter_sr, frequencyFDRep_character, frequencyRepresentation_character_sr,
        mul_zero]

/-- The sign class fixes every frequency class in the representation ring. -/
theorem sign_frequency_class (n : ℕ) [NeZero n] (frequency : ZMod n) :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      TauCeti.SplitK0.of (frequencyFDRep n frequency) =
        TauCeti.SplitK0.of (frequencyFDRep n frequency) := by
  rw [TauCeti.SplitK0.of_mul_of]
  obtain ⟨isomorphism⟩ := sign_frequency_iso n frequency
  exact TauCeti.SplitK0.of_congr isomorphism

/-- Tensoring with sign exchanges the two even rotation-negative scalar representations. -/
theorem sign_even_iso (n : ℕ) [NeZero n] (heven : Even n) (negative : Bool) :
    Nonempty ((signFDRep n ⊗ evenScalarFDRep n heven negative) ≅
      evenScalarFDRep n heven (!negative)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_tensor, Pi.mul_apply, signFDRep_character,
    evenScalarFDRep_character, evenScalarFDRep_character]
  cases element with
  | r coordinate => rw [signCharacter_r, evenScalarCharacter_r, evenScalarCharacter_r, one_mul]
  | sr coordinate =>
      rw [signCharacter_sr, evenScalarCharacter_sr, evenScalarCharacter_sr]
      cases negative <;> norm_num

/-- Sign multiplication exchanges the even scalar classes in the representation ring. -/
theorem sign_even_class (n : ℕ) [NeZero n] (heven : Even n) (negative : Bool) :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      TauCeti.SplitK0.of (evenScalarFDRep n heven negative) =
        TauCeti.SplitK0.of (evenScalarFDRep n heven (!negative)) := by
  rw [TauCeti.SplitK0.of_mul_of]
  obtain ⟨isomorphism⟩ := sign_even_iso n heven negative
  exact TauCeti.SplitK0.of_congr isomorphism

/-- The sign twist of a prefix replaces precisely its trivial summand by sign. -/
theorem sign_partialSum_class (n : ℕ) [NeZero n] (endpoint : ℕ) :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      TauCeti.SplitK0.of (Frequency.partialSum n endpoint) =
        TauCeti.SplitK0.of (Frequency.partialSum n endpoint) +
          TauCeti.SplitK0.of (signFDRep n) -
            TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  apply TauCeti.repRingCharacter_injective
  simp only [map_mul, map_sub, map_add, TauCeti.repRingCharacter_of]
  funext element
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply, FDRep.character_of_trivial]
  cases element with
  | r coordinate => rw [signFDRep_character, signCharacter_r]; ring
  | sr coordinate =>
      rw [signFDRep_character, signCharacter_sr, Frequency.partialSum_character_sr]
      norm_num

end Schubert.Dihedral
