import Schubert.DihedralSplines.RightLowFrequency
import Schubert.Dihedral.FrequencyMultiplicity
import Schubert.DihedralSplines.HessenbergIdealDecomposition
import Schubert.FiniteGroupCharacters.HomMultiplicity

/-! # Exact frequencies in right coordinate kernels -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Positive coefficient degrees remove their binary-form dimensions. -/
theorem removed_boundary_class (half : ℕ) :
    (TauCeti.SplitK0.of (removedFDRep ideal half) : TauCeti.repRing ℂ (DihedralGroup n)) =
      ∑ split : Fin half, (split.val + 2) • TauCeti.SplitK0.of
        (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree (half - (split.val + 1))) := by
  apply TauCeti.repRingCharacter_injective
  funext element
  simp only [map_sum, map_nsmul, TauCeti.repRingCharacter_of, Finset.sum_apply, Pi.smul_apply]
  rw [removed_piece_character]
  apply Finset.sum_congr rfl
  intro split _
  rw [Representation.char_trivial, TauCeti.finrank_homogeneousSubmodule_fin_two]
  rw [RootSubset.Right.pieceFDRep_character]
  simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  congr 1
  ring

/-- A low right quotient has precisely its own positive frequency multiplicity. -/
theorem low_frequency_multiplicity (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 0 < half)
    (degree : ℕ) (hdegree : degree < half)
    (frequency : ℕ) (hfrequency : 0 < frequency) (hbelow : 2 * frequency < n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) =
        if frequency = degree then 1 else 0 := by
  by_cases hzero : degree = 0
  · subst degree
    rw [hom_iso_finrank (frequencyFDRep n frequency)
      (low_zero_iso ideal half hhalf hproper hpositive).some]
    let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
      apply (FDRep.simple_iff_isIrreducible _).mpr
      change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
      infer_instance
    rw [frequency_hom_scalar frequency hfrequency hbelow _ (by
      change Module.finrank ℂ ℂ = 1
      simp)]
    simp only [hfrequency.ne', ite_false]
  · rw [hom_iso_finrank (frequencyFDRep n frequency)
      (low_frequency_iso ideal half hhalf hproper degree (Nat.pos_of_ne_zero hzero) hdegree).some]
    have hmaximum := ideal.card_lt hproper
    exact frequency_hom_frequency frequency degree hfrequency (Nat.pos_of_ne_zero hzero)
      hbelow (by omega)

/-- The right removed kernel has no boundary-frequency copy. -/
theorem removed_frequency_multiplicity (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 0 < half)
    (frequency : ℕ) (hfrequency : 0 < frequency) (hbelow : 2 * frequency < n) :
    Module.finrank ℂ (frequencyFDRep n frequency ⟶ removedFDRep ideal half) =
      if frequency < half then half + 1 - frequency else 0 := by
  classical
  rw [hom_finrank_of_class (frequencyFDRep n frequency) (removedFDRep ideal half)
    (fun split : Fin half => RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
      (half - (split.val + 1))) (fun split => split.val + 2) (removed_boundary_class ideal half)]
  change (∑ split : Fin half, (split.val + 2) * Module.finrank ℂ
    (frequencyFDRep n frequency ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
      (half - (split.val + 1)))) = _
  have hsum :
      (∑ split : Fin half, (split.val + 2) * Module.finrank ℂ
        (frequencyFDRep n frequency ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
          (half - (split.val + 1)))) =
      ∑ split : Fin half, (split.val + 2) *
        (if frequency = half - (split.val + 1) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro split _
    rw [low_frequency_multiplicity ideal half hhalf hproper hpositive
      (half - (split.val + 1)) (by omega) frequency hfrequency hbelow]
  rw [hsum]
  by_cases hless : frequency < half
  · rw [ite_eq_left hless]
    let selected : Fin half := ⟨half - frequency - 1, by omega⟩
    rw [Finset.sum_eq_single selected]
    · have hvalue : half - (selected.val + 1) = frequency := by dsimp [selected]; omega
      simp only [hvalue, ite_true, mul_one]
      dsimp [selected]
      omega
    · intro other _ hother
      have hne : frequency ≠ half - (other.val + 1) := by
        intro heq
        apply hother
        apply Fin.ext
        dsimp [selected]
        omega
      simp only [hne, ite_false, mul_zero]
    · simp
  · rw [ite_eq_right hless]
    apply Finset.sum_eq_zero
    intro split _
    have hne : frequency ≠ half - (split.val + 1) := by omega
    simp only [hne, ite_false, mul_zero]

end Schubert.DihedralSplines.HessenbergIdeal.Right
