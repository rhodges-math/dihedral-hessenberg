import DihedralHessenberg.Dihedral.FrequencyRepresentation
import DihedralHessenberg.Dihedral.FrequencyDistinction
import TauCeti.RepresentationTheory.FDRep

/-! # Finite sums of the positive dihedral frequency objects -/

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Schubert.Dihedral.Frequency

/-- The trivial object together with frequencies one through the specified endpoint. -/
def partialSum (n : ℕ) [NeZero n] : ℕ → FDRep ℂ (DihedralGroup n)
  | 0 => FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)
  | endpoint + 1 => partialSum n endpoint ⊞ frequencyFDRep n (endpoint + 1 : ℕ)

/-- The zero partialSum is the trivial representation. -/
theorem partialSum_zero (n : ℕ) [NeZero n] :
    partialSum n 0 = FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ) := rfl

/-- Enlarging the partialSum adds the next defining frequency object. -/
theorem partialSum_succ (n : ℕ) [NeZero n] (endpoint : ℕ) :
    partialSum n (endpoint + 1) =
      (partialSum n endpoint ⊞ frequencyFDRep n (endpoint + 1 : ℕ)) := rfl

/-- The partialSum character is one plus the sum of its frequency characters. -/
theorem partialSum_character (n : ℕ) [NeZero n] (endpoint : ℕ)
    (element : DihedralGroup n) :
    (partialSum n endpoint).character element =
      1 + ∑ index ∈ Finset.range endpoint,
        (frequencyFDRep n (index + 1 : ℕ)).character element := by
  induction endpoint with
  | zero => simp [partialSum, FDRep.character_of_trivial]
  | succ endpoint hinduction =>
      rw [partialSum_succ, FDRep.char_biprod, Pi.add_apply, hinduction, Finset.sum_range_succ]
      ring

/-- Reflections have partialSum character one. -/
theorem partialSum_character_sr (n : ℕ) [NeZero n] (endpoint : ℕ) (coordinate : ZMod n) :
    (partialSum n endpoint).character (.sr coordinate) = 1 := by
  simp [partialSum_character, frequencyFDRep_character, frequencyRepresentation_character_sr]

/-- The partialSum has dimension one plus twice its endpoint. -/
theorem partialSum_finrank (n : ℕ) [NeZero n] (endpoint : ℕ) :
    Module.finrank ℂ (partialSum n endpoint) = 1 + 2 * endpoint := by
  have hdimension := partialSum_character n endpoint (1 : DihedralGroup n)
  simp only [FDRep.char_one, frequencyFDRep_finrank] at hdimension
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdimension
  have hdimension' : Module.finrank ℂ (partialSum n endpoint) = 1 + endpoint * 2 := by
    exact_mod_cast hdimension
  simpa [Nat.mul_comm] using hdimension'

/-- Below half the rotation order, every added frequency is an irreducible object. -/
theorem partialSum_terms_simple (n : ℕ) [NeZero n] (endpoint : ℕ)
    (hbelow : 2 * endpoint < n) (index : Fin endpoint) :
    CategoryTheory.Simple (frequencyFDRep n (index.val + 1 : ℕ)) := by
  apply frequencyFDRep_simple_of_lower_half
  · omega
  · have hindex := index.isLt
    omega

end Schubert.Dihedral.Frequency
