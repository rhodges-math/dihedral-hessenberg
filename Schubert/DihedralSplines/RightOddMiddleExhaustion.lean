import Schubert.Dihedral.IrrepMultiplicity
import Schubert.DihedralSplines.LeftMiddleMultiplicity
import Schubert.DihedralSplines.RightMiddleMultiplicity
import Schubert.DihedralSplines.OddScalarSurvival
import Schubert.DihedralSplines.OddFrequencySurvival
import Schubert.DihedralSplines.TrivialBoundary
import Schubert.DihedralSplines.MiddleDimension
import Schubert.FiniteGroupCharacters.FrequencyDimensions

/-! # Exact odd middle constituents of quotient representations -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The odd middle action has precisely the saturated scalar and frequency slots. -/
theorem middle_multiplicity_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (simple : Fin 2)
    (witness : MiddleWitness ideal half (simpleRoot n hthree simple) (n - half - 1))
    (index : IrrepIndex n) :
    Module.finrank ℂ (irrepFDRep n index ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
      Sum.elim (fun scalar => if scalar.val = 2 + simple.val then 1 else 0)
        (fun frequency => if half ≤ frequency.val + 1 then 1 else 0) index := by
  classical
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 1 ≤ half := by omega
  have hmaximum := ideal.card_lt hproper
  have hbound : 2 * half < n := by omega
  have hsimple : simpleRoot n hthree simple = simpleRoot n hthree 0 ∨
      simpleRoot n hthree simple = simpleRoot n hthree 1 := by
    fin_cases simple <;> simp
  let lower : IrrepIndex n → ℕ := Sum.elim
    (fun scalar => if scalar.val = 2 + simple.val then 1 else 0)
    (fun frequency => if half ≤ frequency.val + 1 then 1 else 0)
  have hlower (slot : IrrepIndex n) : lower slot ≤ Module.finrank ℂ
      (irrepFDRep n slot ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
    cases slot with
    | inl scalar =>
        change (if scalar.val = 2 + simple.val then 1 else 0) ≤
          Module.finrank ℂ (scalarFDRep n scalar ⟶
            RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half)
        by_cases hselected : scalar.val = 2 + simple.val
        · rw [ite_eq_left hselected]
          have heven : Even n := by
            by_contra hnot
            have hsize := scalar.isLt
            simp only [hnot, ite_false] at hsize
            omega
          have hequal : scalarFDRep n scalar =
              (simpleRoot n hthree simple).scalarFDRep heven := by
            fin_cases simple <;>
              simp [scalarFDRep, hselected, heven, first_simple_scalar,
                second_simple_scalar]
          rw [hequal]
          exact odd_scalar_bound ideal half hcard hproper _ hsimple witness heven
        · rw [ite_eq_right hselected]
          exact Nat.zero_le _
    | inr frequency =>
        change (if half ≤ frequency.val + 1 then 1 else 0) ≤
          Module.finrank ℂ (frequencyFDRep n (frequency.val + 1 : ℕ) ⟶
            RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half)
        by_cases hhigh : half ≤ frequency.val + 1
        · rw [ite_eq_left hhigh]
          have hfrequency : 2 * (frequency.val + 1) < n := by
            have hsize := frequency.isLt
            omega
          exact odd_frequency_bound ideal half hcard hproper _ hsimple witness
            (frequency.val + 1) hhigh hfrequency
        · rw [ite_eq_right hhigh]
          exact Nat.zero_le _
  have hscalar :
      (∑ scalar : Fin (if Even n then 4 else 2),
        if scalar.val = 2 + simple.val then 1 else 0) =
      if Even n then 1 else 0 := by
    by_cases heven : Even n
    · rw [ite_eq_left heven, ite_eq_left heven]
      fin_cases simple <;> decide
    · rw [ite_eq_right heven, ite_eq_right heven]
      fin_cases simple <;> decide
  have hbudget : ∑ slot, lower slot * Sum.elim (fun _ => 1) (fun _ => 2) slot =
      Module.finrank ℂ (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
    rw [Fintype.sum_sum_type, middle_dimension_odd ideal half hcard]
    change (∑ scalar : Fin (if Even n then 4 else 2),
        (if scalar.val = 2 + simple.val then 1 else 0) * 1) +
      (∑ frequency : Fin ((n - 1) / 2),
        (if half ≤ frequency.val + 1 then 1 else 0) * 2) = _
    simp only [mul_one, mul_comm _ 2, ← Finset.mul_sum, hscalar]
    have hformula := odd_right_budget n half hpositive hbound
    omega
  exact irrep_multiplicities_exhausted
    (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) lower hlower hbudget index

end Schubert.DihedralSplines.HessenbergIdeal.Right
