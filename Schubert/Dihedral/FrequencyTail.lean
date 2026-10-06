import Schubert.FiniteGroupCharacters.FiniteSum
import Schubert.Dihedral.CosetDecomposition

/-! # Frequency tails and effective coset complements -/

noncomputable section

open CategoryTheory Limits
open scoped BigOperators

namespace Schubert.Dihedral.Frequency

/-- The finite direct sum of consecutive frequencies after a prefix. -/
def tail (n : ℕ) [NeZero n] (start count : ℕ) : FDRep ℂ (DihedralGroup n) :=
  ⨁ fun index : Fin count => frequencyFDRep n (start + index.val + 1 : ℕ)

/-- The trace of a frequency tail is its finite sum of frequency traces. -/
theorem tail_character (n : ℕ) [NeZero n] (start count : ℕ) (element : DihedralGroup n) :
    (tail n start count).character element =
      ∑ index ∈ Finset.range count,
        (frequencyFDRep n (start + index + 1 : ℕ)).character element := by
  rw [tail, Schubert.FiniteGroupCharacters.finiteSum_character, Finset.sum_apply]
  exact Fin.sum_univ_eq_sum_range
    (fun index : ℕ => (frequencyFDRep n (start + index + 1 : ℕ)).character element) count

/-- A prefix splits as its shorter prefix and the remaining direct sum. -/
theorem partialSum_split (n : ℕ) [NeZero n] (start count : ℕ) :
    Nonempty (partialSum n (start + count) ≅ (partialSum n start ⊞ tail n start count)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [partialSum_character, FDRep.char_biprod, Pi.add_apply, partialSum_character,
    tail_character, Finset.sum_range_add]
  simp only [Nat.add_assoc]
  ring

/-- Prefix splitting gives its exact equality in the representation ring. -/
theorem partialSum_split_class (n : ℕ) [NeZero n] (start count : ℕ) :
    (TauCeti.SplitK0.of (partialSum n (start + count)) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
        TauCeti.SplitK0.of (partialSum n start) + TauCeti.SplitK0.of (tail n start count) := by
  obtain ⟨isomorphism⟩ := partialSum_split n start count
  exact (TauCeti.SplitK0.of_congr isomorphism).trans (TauCeti.SplitK0.of_biprod _ _)

/-- All tail summands are irreducible when their endpoint is below half the rotation order. -/
theorem tail_terms_simple (n : ℕ) [NeZero n] (start count : ℕ)
    (hbelow : 2 * (start + count) < n) (index : Fin count) :
    Simple (frequencyFDRep n (start + index.val + 1 : ℕ)) := by
  apply frequencyFDRep_simple_of_lower_half
  · omega
  · have hindex := index.isLt
    omega

end Schubert.Dihedral.Frequency

namespace Schubert.Dihedral.PositiveRoot

/-- An odd coset's virtual prefix complement is the class of a frequency tail. -/
theorem coset_odd_complement {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (hodd : Odd n) (start : ℕ) (hbound : start ≤ (n - 1) / 2) :
    (TauCeti.SplitK0.of alpha.cosetFDRep : TauCeti.repRing ℂ (DihedralGroup n)) -
      TauCeti.SplitK0.of (Frequency.partialSum n start) =
        TauCeti.SplitK0.of (Frequency.tail n start ((n - 1) / 2 - start)) := by
  rw [coset_odd_class alpha hodd]
  have hsplit := Frequency.partialSum_split_class n start ((n - 1) / 2 - start)
  rw [Nat.add_sub_of_le hbound] at hsplit
  rw [hsplit]
  abel

/-- An even coset complement is its scalar character plus a frequency tail. -/
theorem coset_even_complement {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (heven : Even n) (start : ℕ) (hbound : start ≤ n / 2 - 1) :
    (TauCeti.SplitK0.of alpha.cosetFDRep : TauCeti.repRing ℂ (DihedralGroup n)) -
      TauCeti.SplitK0.of (Frequency.partialSum n start) =
        TauCeti.SplitK0.of (alpha.scalarFDRep heven) +
          TauCeti.SplitK0.of (Frequency.tail n start (n / 2 - 1 - start)) := by
  rw [coset_even_class alpha heven]
  have hsplit := Frequency.partialSum_split_class n start (n / 2 - 1 - start)
  rw [Nat.add_sub_of_le hbound] at hsplit
  rw [hsplit]
  abel

end Schubert.Dihedral.PositiveRoot
