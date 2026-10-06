import Schubert.Dihedral.FrequencyEigenbasis
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Distinction of the dihedral frequency representations

The rotation trace separates frequencies in the first half of the period, so their
finite-dimensional representation objects can be isomorphic only at equal indices.
-/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral

/-- Lower-half frequency objects are isomorphic exactly when their frequencies agree. -/
theorem frequencyFDRep_iso_iff_frequency_eq (n : ℕ) [NeZero n] (first second : ℕ)
    (hfirst : 2 * first < n) (hsecond : 2 * second < n) :
    Nonempty (frequencyFDRep n first ≅ frequencyFDRep n second) ↔ first = second := by
  constructor
  · rintro ⟨isomorphism⟩
    have hequal := congrFun (FDRep.char_iso isomorphism) (rotation n)
    rw [frequencyFDRep_character, frequencyFDRep_character,
      _root_.Schubert.Dihedral.Frequency.character_rotation,
        _root_.Schubert.Dihedral.Frequency.character_rotation,
      ZMod.val_natCast_of_lt (show first < n by omega),
      ZMod.val_natCast_of_lt (show second < n by omega)] at hequal
    apply (rotationEigenvalue_inverse_sum_eq_iff n first second hfirst hsecond).mp
    simpa only [inv_pow, add_comm] using hequal
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Every positive lower-half frequency object is simple. -/
theorem frequencyFDRep_simple_of_lower_half (n : ℕ) [NeZero n] (frequency : ℕ)
    (hpositive : 0 < frequency) (hbelow : 2 * frequency < n) :
    CategoryTheory.Simple (frequencyFDRep n frequency) := by
  apply frequencyFDRep_simple
  rw [ZMod.val_natCast_of_lt (show frequency < n by omega)]
  intro hdivisible
  have hzero := Nat.eq_zero_of_dvd_of_lt hdivisible hbelow
  omega

end Schubert.Dihedral
