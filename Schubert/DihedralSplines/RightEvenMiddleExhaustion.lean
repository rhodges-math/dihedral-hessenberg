import Schubert.Dihedral.IrrepMultiplicity
import Schubert.DihedralSplines.LeftMiddleMultiplicity
import Schubert.DihedralSplines.RightMiddleMultiplicity
import Schubert.DihedralSplines.MiddleScalarSurvival
import Schubert.DihedralSplines.TrivialBoundary
import Schubert.DihedralSplines.MiddleDimension
import Schubert.FiniteGroupCharacters.FrequencyDimensions

/-! # Exact even middle constituents of quotient representations -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The even middle action has precisely the saturated scalar and frequency slots. -/
theorem middle_multiplicity_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n) (index : IrrepIndex n) :
    Module.finrank ℂ (irrepFDRep n index ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
      Sum.elim (fun scalar => if 2 ≤ scalar.val then 1 else 0)
        (fun frequency => if half ≤ frequency.val + 1 then 2 else 0) index := by
  classical
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hpositive : 1 ≤ half := by omega
  have hmaximum := ideal.card_lt hproper
  have hbound : 2 * half < n := by omega
  obtain ⟨first⟩ := ideal.middle_even half hcard hproper (simpleRoot n hthree 0) (Or.inl rfl)
  obtain ⟨second⟩ := ideal.middle_even half hcard hproper (simpleRoot n hthree 1) (Or.inr rfl)
  let lower : IrrepIndex n → ℕ := Sum.elim
    (fun scalar => if 2 ≤ scalar.val then 1 else 0)
    (fun frequency => if half ≤ frequency.val + 1 then 2 else 0)
  have hlower (slot : IrrepIndex n) : lower slot ≤ Module.finrank ℂ
      (irrepFDRep n slot ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
    cases slot with
    | inl scalar =>
        change (if 2 ≤ scalar.val then 1 else 0) ≤
          Module.finrank ℂ (scalarFDRep n scalar ⟶
            RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half)
        by_cases htwo : 2 ≤ scalar.val
        · rw [ite_eq_left htwo]
          have heven : Even n := by
            by_contra hnot
            have hsize := scalar.isLt
            simp only [hnot, ite_false] at hsize
            omega
          rw [scalarFDRep, ite_eq_right (show scalar.val ≠ 0 by omega),
            ite_eq_right (show scalar.val ≠ 1 by omega), dite_eq_left heven]
          exact middle_scalar_bound ideal half hcard hproper first second heven _
        · rw [ite_eq_right htwo]
          exact Nat.zero_le _
    | inr frequency =>
        change (if half ≤ frequency.val + 1 then 2 else 0) ≤
          Module.finrank ℂ (frequencyFDRep n (frequency.val + 1 : ℕ) ⟶
            RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half)
        by_cases hlow : frequency.val + 1 < half
        · simp only [show ¬ half ≤ frequency.val + 1 by omega, ite_false]
          exact Nat.zero_le _
        · have hfrequency : 2 * (frequency.val + 1) < n := by
            have hsize := frequency.isLt
            omega
          have hsurvive := middle_frequency_bound ideal half hcard hproper first second
            (frequency.val + 1) (by omega) hfrequency
          rw [ite_eq_left (show half ≤ frequency.val + 1 by omega)]
          exact hsurvive
  have hscalar :
      (∑ scalar : Fin (if Even n then 4 else 2),
        if 2 ≤ scalar.val then 1 else 0) =
      if Even n then 2 else 0 := by
    by_cases heven : Even n
    · rw [ite_eq_left heven, ite_eq_left heven]
      decide
    · rw [ite_eq_right heven, ite_eq_right heven]
      decide
  have hbudget : ∑ slot, lower slot * Sum.elim (fun _ => 1) (fun _ => 2) slot =
      Module.finrank ℂ (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
    rw [Fintype.sum_sum_type, middle_dimension_even ideal half hcard]
    change (∑ scalar : Fin (if Even n then 4 else 2),
        (if 2 ≤ scalar.val then 1 else 0) * 1) +
      (∑ frequency : Fin ((n - 1) / 2),
        (if half ≤ frequency.val + 1 then 2 else 0) * 2) = _
    simp only [mul_one, mul_comm _ 2, ← Finset.mul_sum, hscalar]
    have hformula := even_right_budget n half hpositive hbound
    omega
  exact irrep_multiplicities_exhausted
    (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) lower hlower hbudget index

end Schubert.DihedralSplines.HessenbergIdeal.Right
