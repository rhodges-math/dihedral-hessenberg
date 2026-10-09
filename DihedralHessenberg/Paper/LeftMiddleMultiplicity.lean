import DihedralHessenberg.Paper.LeftRemovedMultiplicity
import DihedralHessenberg.Paper.QuotientSurvival
import DihedralHessenberg.FiniteGroupCharacters.SimpleEmbedding

/-! # Surviving frequency multiplicities in the even middle quotient -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Joint middle orbits leave one boundary and two higher frequency copies. -/
theorem middle_frequency_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (frequency : ℕ) (hfrequency : half ≤ frequency) (hbelow : 2 * frequency < n) :
    (if frequency = half then 1 else 2) ≤ Module.finrank ℂ
      (frequencyFDRep n frequency ⟶ RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 1 ≤ half := by omega
  have hfrequencyPositive : 0 < frequency := by omega
  have hbound := middle_coset_survival ideal half hcard hproper first second
    (frequencyFDRep n frequency)
  rw [frequency_hom_coset_pair frequency hfrequencyPositive hbelow,
    removed_frequency_multiplicity ideal half (by omega) hproper hpositive
      frequency hfrequencyPositive hbelow] at hbound
  split_ifs at hbound ⊢ <;> omega

/-- Every boundary or higher lower-half frequency has a middle quotient embedding. -/
theorem middle_frequency_embedding (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (frequency : ℕ) (hfrequency : half ≤ frequency) (hbelow : 2 * frequency < n) :
    ∃ embedding : Representation.IntertwiningMap (frequencyFDRep n frequency).ρ
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree half),
      Function.Injective embedding := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  let : Simple (frequencyFDRep n frequency) :=
    frequencyFDRep_simple_of_lower_half n frequency (by omega) hbelow
  apply simple_embedding_of_hom_pos (frequencyFDRep n frequency)
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half)
  have hbound := middle_frequency_bound ideal half hcard hproper first second
    frequency hfrequency hbelow
  split_ifs at hbound <;> omega

end Schubert.DihedralSplines.HessenbergIdeal.Left
