import Schubert.DihedralSplines.OddCosetSurvival
import Schubert.DihedralSplines.LeftRemovedMultiplicity
import Schubert.DihedralSplines.RightRemovedMultiplicity

/-! # Exact odd middle frequency survival bounds -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Every unremoved odd middle frequency remains in the quotient. -/
theorem odd_frequency_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1)) (frequency : ℕ)
    (hfrequency : half < frequency) (hbelow : 2 * frequency < n) :
    1 ≤ Module.finrank ℂ (frequencyFDRep n frequency ⟶
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 0 < frequency := by omega
  have hbound := odd_coset_survival ideal half hcard hproper alpha hsimple witness
    (frequencyFDRep n frequency)
  rw [frequency_hom_coset frequency hpositive hbelow,
    removed_frequency_multiplicity ideal half (by omega) hproper (by omega)
      frequency hpositive hbelow] at hbound
  split_ifs at hbound <;> omega
end Left

namespace Right
/-- Every unremoved odd middle frequency remains in the quotient. -/
theorem odd_frequency_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1)) (frequency : ℕ)
    (hfrequency : half ≤ frequency) (hbelow : 2 * frequency < n) :
    1 ≤ Module.finrank ℂ (frequencyFDRep n frequency ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 0 < frequency := by omega
  have hbound := odd_coset_survival ideal half hcard hproper alpha hsimple witness
    (frequencyFDRep n frequency)
  rw [frequency_hom_coset frequency hpositive hbelow,
    removed_frequency_multiplicity ideal half (by omega) hproper (by omega)
      frequency hpositive hbelow] at hbound
  split_ifs at hbound <;> omega
end Right

end Schubert.DihedralSplines.HessenbergIdeal
