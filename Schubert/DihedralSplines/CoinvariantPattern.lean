import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.Dihedral.ScalarCharacters
import Schubert.Dihedral.FrequencyRepresentation
import Schubert.FiniteGroupCharacters.GradedClass
import Schubert.DihedralSplines.HessenbergBasic
import Schubert.Dihedral.FrequencyDistinction
import Schubert.Dihedral.SignScalarProducts
import Schubert.Dihedral.CoinvariantGradedClass
import Schubert.FiniteGroupCharacters.ShiftedSeries

/-! # The truncated coinvariant expression for a Hessenberg ideal -/

noncomputable section

open scoped BigOperators

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)

/-- The finite representation-ring expression Co_H with its reflected frequency degrees. -/
def coClass : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) := by
  let : NeZero n := ⟨by omega⟩
  exact PowerSeries.mk fun degree =>
    if degree = 0 then
      TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ))
    else if degree = ideal.carrier.ncard then TauCeti.SplitK0.of (signFDRep n)
    else if degree < ideal.carrier.ncard then
      TauCeti.SplitK0.of (frequencyFDRep n (min degree (ideal.carrier.ncard - degree) : ℕ))
    else 0

/-- Each coefficient is the trivial, reflected frequency, sign, or zero class. -/
theorem coClass_coeff [NeZero n] (degree : ℕ) :
    PowerSeries.coeff degree ideal.coClass =
      if degree = 0 then
        (TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) :
          TauCeti.repRing ℂ (DihedralGroup n))
      else if degree = ideal.carrier.ncard then TauCeti.SplitK0.of (signFDRep n)
      else if degree < ideal.carrier.ncard then
        TauCeti.SplitK0.of (frequencyFDRep n (min degree (ideal.carrier.ncard - degree) : ℕ))
      else 0 := by
  simp only [coClass, PowerSeries.coeff_mk]

/-- Co_H has no coefficients above the number of selected roots. -/
theorem coClass_coeff_above [NeZero n] (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    PowerSeries.coeff degree ideal.coClass = 0 := by
  rw [coClass_coeff]
  simp only [show degree ≠ 0 by omega, habove.ne', habove.not_gt, ite_false]

/-- The degree-zero coefficient is the class of the trivial representation. -/
theorem coClass_coeff_zero [NeZero n] :
    PowerSeries.coeff 0 ideal.coClass =
      TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  rw [coClass_coeff, ite_eq_left rfl]

/-- The top coefficient is the class of the determinant sign representation. -/
theorem coClass_coeff_top [NeZero n] :
    PowerSeries.coeff ideal.carrier.ncard ideal.coClass = TauCeti.SplitK0.of (signFDRep n) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed] at hminimum
  rw [coClass_coeff, ite_eq_right (show ideal.carrier.ncard ≠ 0 by omega), ite_eq_left rfl]

/-- A positive degree through the lower half has its positive frequency class. -/
theorem coClass_coeff_lower [NeZero n] (degree : ℕ) (hpositive : 0 < degree)
    (hinterior : degree < ideal.carrier.ncard) (hhalf : 2 * degree ≤ ideal.carrier.ncard) :
    PowerSeries.coeff degree ideal.coClass =
      TauCeti.SplitK0.of (frequencyFDRep n degree) := by
  rw [coClass_coeff]
  simp only [hpositive.ne', hinterior.ne, hinterior, ite_false, ite_true,
    min_eq_left (show degree ≤ ideal.carrier.ncard - degree by omega)]

/-- A positive interior upper degree has the reflected lower frequency class. -/
theorem coClass_coeff_upper [NeZero n] (degree : ℕ) (hpositive : 0 < degree)
    (hinterior : degree < ideal.carrier.ncard) (hhalf : ideal.carrier.ncard ≤ 2 * degree) :
    PowerSeries.coeff degree ideal.coClass =
      TauCeti.SplitK0.of (frequencyFDRep n (ideal.carrier.ncard - degree : ℕ)) := by
  rw [coClass_coeff]
  simp only [hpositive.ne', hinterior.ne, hinterior, ite_false, ite_true,
    min_eq_right (show ideal.carrier.ncard - degree ≤ degree by omega)]

/-- The displayed expression is a finite monomial sum on the root cardinality. -/
theorem coClass_eq_sum [NeZero n] :
    ideal.coClass = ∑ degree ∈ Finset.range (ideal.carrier.ncard + 1),
      PowerSeries.monomial degree (PowerSeries.coeff degree ideal.coClass) := by
  ext degree
  rw [map_sum]
  simp only [PowerSeries.coeff_monomial]
  by_cases hbelow : degree < ideal.carrier.ncard + 1
  · simp [hbelow]
  · rw [coClass_coeff_above ideal degree (by omega)]
    simp [hbelow]

/-- Every interior frequency is irreducible for a proper root cardinality. -/
theorem coClass_frequency_simple [NeZero n] (hproper : ideal.carrier.ncard < n)
    (degree : ℕ) (hpositive : 0 < degree) (hinterior : degree < ideal.carrier.ncard) :
    CategoryTheory.Simple
      (frequencyFDRep n (min degree (ideal.carrier.ncard - degree) : ℕ)) := by
  apply frequencyFDRep_simple_of_lower_half
  · exact lt_min hpositive (Nat.sub_pos_of_lt hinterior)
  · have hfirst := min_le_left degree (ideal.carrier.ncard - degree)
    have hsecond := min_le_right degree (ideal.carrier.ncard - degree)
    omega

/-- The finite Co_H expression has the sign-twisted reversal symmetry in every degree. -/
theorem coClass_sign_duality [NeZero n] (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      PowerSeries.coeff (ideal.carrier.ncard - degree) ideal.coClass =
        PowerSeries.coeff degree ideal.coClass := by
  by_cases hzero : degree = 0
  · subst degree
    rw [Nat.sub_zero, coClass_coeff_top, coClass_coeff_zero]
    exact sign_square_class n
  by_cases htop : degree = ideal.carrier.ncard
  · subst degree
    rw [Nat.sub_self, coClass_coeff_zero, coClass_coeff_top]
    exact sign_trivial_class n
  have hinterior : degree < ideal.carrier.ncard := by omega
  have hreverse : ideal.carrier.ncard - degree < ideal.carrier.ncard := by omega
  rw [coClass_coeff, ite_eq_right (show ideal.carrier.ncard - degree ≠ 0 by omega),
    ite_eq_right hreverse.ne, ite_eq_left hreverse]
  rw [coClass_coeff, ite_eq_right hzero, ite_eq_right htop, ite_eq_left hinterior]
  rw [Nat.sub_sub_self hdegree, min_comm]
  exact sign_frequency_class n _

/-- Through the lower half, Co_H uses exactly the coinvariant degree classes. -/
theorem coClass_coeff_coinvariant [NeZero n] (hproper : ideal.carrier.ncard < n)
    (degree : ℕ) (hhalf : 2 * degree ≤ ideal.carrier.ncard) :
    PowerSeries.coeff degree ideal.coClass =
      PowerSeries.coeff degree (Coinvariant.gradedClass n) := by
  by_cases hzero : degree = 0
  · subst degree
    rw [coClass_coeff_zero, Coinvariant.gradedClass_coeff n hthree]
    simp only [ite_true]
  · have hpositive : 0 < degree := by omega
    have hinterior : degree < ideal.carrier.ncard := by omega
    have hbelow : degree < n := by omega
    rw [coClass_coeff_lower ideal degree hpositive hinterior hhalf,
      Coinvariant.gradedClass_coeff n hthree]
    simp only [hzero, hbelow.ne, hbelow, ite_false, ite_true]

/-- Even cardinality gives the displayed ascending and descending frequency series. -/
theorem coClass_even [NeZero n] (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half) :
    ideal.coClass =
      PowerSeries.monomial 0
        (TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ))) +
      (∑ index ∈ Finset.range half, PowerSeries.monomial (1 + index)
        (TauCeti.SplitK0.of (frequencyFDRep n (index + 1 : ℕ)))) +
      (∑ index ∈ Finset.range (half - 1), PowerSeries.monomial (half + 1 + index)
        (TauCeti.SplitK0.of (frequencyFDRep n (half - 1 - index : ℕ)))) +
      PowerSeries.monomial (2 * half) (TauCeti.SplitK0.of (signFDRep n)) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  ext degree
  rw [coClass_coeff, hcard]
  simp only [map_add, PowerSeries.coeff_monomial]
  rw [Schubert.FiniteGroupCharacters.shifted_sum_coeff,
    Schubert.FiniteGroupCharacters.shifted_sum_coeff]
  split_ifs <;> try omega
  all_goals simp only [zero_add, add_zero]
  all_goals apply congrArg (fun index : ℕ =>
    (TauCeti.SplitK0.of (frequencyFDRep n index) : TauCeti.repRing ℂ (DihedralGroup n)))
  all_goals omega

/-- Odd cardinality repeats its middle frequency in the two neighboring middle degrees. -/
theorem coClass_odd [NeZero n] (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1) :
    ideal.coClass =
      PowerSeries.monomial 0
        (TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ))) +
      (∑ index ∈ Finset.range half, PowerSeries.monomial (1 + index)
        (TauCeti.SplitK0.of (frequencyFDRep n (index + 1 : ℕ)))) +
      (∑ index ∈ Finset.range half, PowerSeries.monomial (half + 1 + index)
        (TauCeti.SplitK0.of (frequencyFDRep n (half - index : ℕ)))) +
      PowerSeries.monomial (2 * half + 1) (TauCeti.SplitK0.of (signFDRep n)) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  ext degree
  rw [coClass_coeff, hcard]
  simp only [map_add, PowerSeries.coeff_monomial]
  rw [Schubert.FiniteGroupCharacters.shifted_sum_coeff,
    Schubert.FiniteGroupCharacters.shifted_sum_coeff]
  split_ifs <;> try omega
  all_goals simp only [zero_add, add_zero]
  all_goals apply congrArg (fun index : ℕ =>
    (TauCeti.SplitK0.of (frequencyFDRep n index) : TauCeti.repRing ℂ (DihedralGroup n)))
  all_goals omega

end Schubert.DihedralSplines.HessenbergIdeal
