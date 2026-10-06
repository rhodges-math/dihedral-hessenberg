import Schubert.FiniteGroupCharacters.ClassMultiplicity
import Schubert.DihedralSplines.RightEvenMiddleExhaustion
import Schubert.Dihedral.ScalarSlotMultiplicity
import Schubert.Dihedral.SimpleScalar

/-! # Virtual coset formulas for even middle quotients -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The even middle quotient is the boundary frequency plus its coset complement. -/
theorem middle_class_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    (TauCeti.SplitK0.of (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (frequencyFDRep n half) +
      TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
      TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
      TauCeti.SplitK0.of (Frequency.partialSum n half) -
      TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)) := by
  classical
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 1 ≤ half := by omega
  have hmaximum := ideal.card_lt hproper
  have hbound : 2 * half < n := by omega
  apply class_eq_of_multiplicities (irrepFDRep n) (irrepFDRep_simple n)
    (fun first second => (irrepFDRep_iso_iff_eq n first second).mp) (irrepIndex_card n)
  intro index
  cases index with
  | inl scalar =>
      let : Simple (scalarFDRep n scalar) := scalarFDRep_simple n scalar
      change classMultiplicity (scalarFDRep n scalar) _ =
        classMultiplicity (scalarFDRep n scalar) _
      simp only [map_sub, map_add, classMultiplicity_of]
      have hmult : Module.finrank ℂ (scalarFDRep n scalar ⟶
          RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
          if 2 ≤ scalar.val then 1 else 0 :=
        middle_multiplicity_even ideal half hcard hproper (Sum.inl scalar)
      rw [hmult]
      rw [scalar_hom_frequency _ (ScalarFamily.finrank n scalar) half (by omega) hbound,
        scalar_hom_prefix _ (ScalarFamily.finrank n scalar) half hbound,
        scalar_hom_prefix _ (ScalarFamily.finrank n scalar) (half - 1) (by omega),
        scalar_hom_coset _ (ScalarFamily.finrank n scalar),
        scalar_hom_coset _ (ScalarFamily.finrank n scalar)]
      simp_rw [scalar_hom_trivial]
      by_cases heven : Even n
      · rw [dite_eq_left heven, dite_eq_left heven, first_simple_scalar n hthree heven,
          second_simple_scalar n hthree heven, scalar_hom_even_slot scalar heven false,
          scalar_hom_even_slot scalar heven true]
        have hsize := scalar.isLt
        simp only [heven, ite_true] at hsize
        have hcases : scalar.val = 0 ∨ scalar.val = 1 ∨ scalar.val = 2 ∨ scalar.val = 3 := by
          omega
        rcases hcases with hval | hval | hval | hval <;> norm_num [hval]
      · rw [dite_eq_right heven, dite_eq_right heven]
        have hsize := scalar.isLt
        simp only [heven, ite_false] at hsize
        have hcases : scalar.val = 0 ∨ scalar.val = 1 := by omega
        rcases hcases with hval | hval <;> norm_num [hval]
  | inr frequency =>
      change classMultiplicity (frequencyFDRep n (frequency.val + 1 : ℕ)) _ =
        classMultiplicity (frequencyFDRep n (frequency.val + 1 : ℕ)) _
      simp only [map_sub, map_add, classMultiplicity_of]
      have hmult : Module.finrank ℂ (frequencyFDRep n (frequency.val + 1 : ℕ) ⟶
          RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
          if half ≤ frequency.val + 1 then 2 else 0 :=
        middle_multiplicity_even ideal half hcard hproper (Sum.inr frequency)
      rw [hmult]
      have hfrequency : 2 * (frequency.val + 1) < n := by
        have hsize := frequency.isLt
        omega
      rw [frequency_hom_frequency (frequency.val + 1) half (by omega) (by omega)
          hfrequency hbound, frequency_hom_coset (frequency.val + 1) (by omega) hfrequency,
        frequency_hom_coset (frequency.val + 1) (by omega) hfrequency,
        frequency_hom_prefix (frequency.val + 1) (by omega) hfrequency half hbound,
        frequency_hom_prefix (frequency.val + 1) (by omega) hfrequency (half - 1) (by omega)]
      split_ifs <;> norm_num <;> omega

end Schubert.DihedralSplines.HessenbergIdeal.Right
