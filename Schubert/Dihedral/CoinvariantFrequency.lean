import Schubert.Dihedral.FrequencyPower
import Schubert.Dihedral.CoinvariantMiddleCharacters
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Frequency decomposition of middle coinvariant degree pieces -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.Coinvariant.Middle

/-- Each middle coinvariant degree is the defining frequency pullback of its degree. -/
theorem frequency_iso (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (hpositive : 0 < degree) (hbelow : degree < n) :
    Nonempty (coinvariantPieceFDRep n degree ≅ frequencyFDRep n degree) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  cases element with
  | r coordinate =>
      rw [character_r n hthree degree hpositive hbelow,
        Frequency.character_additive, AddChar.map_neg_eq_inv,
        Frequency.additive_nat_mul, Frequency.additive_exp]
      simp only [inv_pow]
      ring
  | sr coordinate =>
      rw [character_sr n hthree degree hpositive hbelow, frequencyFDRep_character,
        frequencyRepresentation_character_sr]

end Schubert.Dihedral.Coinvariant.Middle
