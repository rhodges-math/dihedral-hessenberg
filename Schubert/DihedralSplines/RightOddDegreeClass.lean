import Schubert.DihedralSplines.QuotientClassSupport
import Schubert.DihedralSplines.MiddleDominantClass
import Schubert.Dihedral.SignCoset
import Schubert.DihedralSplines.RightLowFrequency
import Schubert.DihedralSplines.QuotientSymmetry
import Schubert.DihedralSplines.CoinvariantPattern

/-! # All-degree virtual classes of odd right quotients -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Each odd right degree is its coinvariant class and exact middle complement. -/
theorem piece_class_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : ideal.IsDominant alpha) (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      PowerSeries.coeff degree ideal.coClass +
      (if degree = half then TauCeti.SplitK0.of alpha.cosetFDRep -
        TauCeti.SplitK0.of (Frequency.partialSum n half) else 0) +
      if degree = half + 1 then TauCeti.SplitK0.of beta.cosetFDRep -
        TauCeti.SplitK0.of (Frequency.partialSum n half) else 0 := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 0 < half := by omega
  by_cases hmiddle : degree = half
  · subst degree
    rw [middle_class_dominant ideal half hcard hproper alpha hdominant,
      coClass_coeff_lower ideal half hpositive (by omega) (by omega), ite_eq_left rfl,
      ite_eq_right (show half ≠ half + 1 by omega), add_zero]
    abel
  rw [ite_eq_right hmiddle, add_zero]
  by_cases hupper : degree = half + 1
  · subst degree
    have hcomplement : ideal.carrier.ncard - (half + 1) = half := by omega
    have hmiddleFormula : (TauCeti.SplitK0.of
        (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) :
        TauCeti.repRing ℂ (DihedralGroup n)) =
        TauCeti.SplitK0.of (frequencyFDRep n half) +
          (TauCeti.SplitK0.of alpha.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half)) := by
      rw [middle_class_dominant ideal half hcard hproper alpha hdominant]
      abel
    rw [ite_eq_left rfl, TauCeti.SplitK0.of_congr
      (sign_complementary ideal (half + 1) (by omega)).some.symm,
      ← TauCeti.SplitK0.of_mul_of, hcomplement, hmiddleFormula,
      mul_add, sign_frequency_class, sign_coset_complement hthree alpha beta hpair,
      coClass_coeff_upper ideal (half + 1) (by omega) (by omega) (by omega), hcomplement]
  rw [ite_eq_right hupper, add_zero]
  by_cases habove : ideal.carrier.ncard < degree
  · rw [piece_class_above ideal degree habove, coClass_coeff_above ideal degree habove]
  have hbelow : degree ≤ ideal.carrier.ncard := by omega
  by_cases hzero : degree = 0
  · subst degree
    rw [TauCeti.SplitK0.of_congr (low_zero_iso ideal half (by omega) hproper hpositive).some,
      coClass_coeff_zero]
  by_cases htop : degree = ideal.carrier.ncard
  · subst degree
    rw [TauCeti.SplitK0.of_congr (top_iso ideal).some, coClass_coeff_top]
  by_cases hlow : degree < half
  · rw [TauCeti.SplitK0.of_congr
        (low_frequency_iso ideal half (by omega) hproper degree (by omega) hlow).some,
      coClass_coeff_lower ideal degree (by omega) (by omega) (by omega)]
  have hcomplement : ideal.carrier.ncard - degree < half := by omega
  rw [TauCeti.SplitK0.of_congr (sign_complementary ideal degree hbelow).some.symm,
    ← TauCeti.SplitK0.of_mul_of,
    TauCeti.SplitK0.of_congr (low_frequency_iso ideal half (by omega) hproper
      (ideal.carrier.ncard - degree) (by omega) hcomplement).some,
    sign_frequency_class,
    coClass_coeff_upper ideal degree (by omega) (by omega) (by omega)]

end Schubert.DihedralSplines.HessenbergIdeal.Right
