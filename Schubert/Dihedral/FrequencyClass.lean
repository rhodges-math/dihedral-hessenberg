import Schubert.Dihedral.FrequencySum
import Schubert.FiniteGroupCharacters.ClassDimension

/-! # Classes of finite sums of the frequency representations -/

noncomputable section

namespace Schubert.Dihedral.Frequency

open Schubert.FiniteGroupCharacters
open scoped BigOperators

/-- The frequency sum separates its trivial and defining terms from the higher frequencies. -/
theorem partialSum_after_one (n : ℕ) [NeZero n] (endpoint : ℕ) (hpositive : 1 ≤ endpoint) :
    (TauCeti.SplitK0.of (partialSum n endpoint) : TauCeti.repRing ℂ (DihedralGroup n)) =
      1 + TauCeti.SplitK0.of (frequencyFDRep n 1) +
        ∑ frequency ∈ Finset.Icc 2 endpoint,
          TauCeti.SplitK0.of (frequencyFDRep n frequency) := by
  induction endpoint, hpositive using Nat.le_induction with
  | base =>
      simp [partialSum_succ, partialSum_zero, TauCeti.SplitK0.of_biprod,
        trivial_class_one]
  | succ endpoint hpositive hinduction =>
      rw [partialSum_succ, TauCeti.SplitK0.of_biprod, hinduction,
        Finset.sum_Icc_succ_top (by omega)]
      abel

end Schubert.Dihedral.Frequency
