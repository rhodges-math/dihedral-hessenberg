import DihedralHessenberg.Paper.LeftEvenClass
import DihedralHessenberg.Paper.LeftOddClass
import DihedralHessenberg.Paper.RightEvenClass
import DihedralHessenberg.Paper.RightOddClass

/-! # Complete graded class formulas on Hessenberg quotients -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- The graded quotient action has the complete parity-specific class formula. -/
theorem graded_class (hproper : ideal.carrier ≠ positiveRoots n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : Odd ideal.carrier.ncard → ideal.IsDominant alpha) :
    let half := ideal.carrier.ncard / 2
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      if Even ideal.carrier.ncard then
        (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half),
          (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
        PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep + TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half) -
            TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)))
      else
        (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half + 1),
          (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
        (PowerSeries.X ^ half + PowerSeries.X ^ (half + 1)) * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half)) := by
  dsimp only
  by_cases heven : Even ideal.carrier.ncard
  · rw [ite_eq_left heven]
    have hcard : ideal.carrier.ncard = 2 * (ideal.carrier.ncard / 2) := by
      obtain ⟨height, hheight⟩ := heven
      omega
    have hformula := graded_class_even ideal (ideal.carrier.ncard / 2) hcard hproper
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hformula
    · rw [add_comm (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep)
        (TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep)] at hformula
      exact hformula
  · rw [ite_eq_right heven]
    have hodd := Nat.not_even_iff_odd.mp heven
    have hcard : ideal.carrier.ncard = 2 * (ideal.carrier.ncard / 2) + 1 := by
      obtain ⟨height, hheight⟩ := hodd
      omega
    exact graded_class_odd ideal _ hcard hproper alpha (hdominant hodd)
end Left

namespace Right
/-- The graded quotient action has the complete parity-specific class formula. -/
theorem graded_class (hproper : ideal.carrier ≠ positiveRoots n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : Odd ideal.carrier.ncard → ideal.IsDominant alpha) :
    let half := ideal.carrier.ncard / 2
    RootSubset.Right.gradedClass ideal.toRootSubset hthree =
      if Even ideal.carrier.ncard then
        ideal.coClass +
        PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep + TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half) -
            TauCeti.SplitK0.of (Frequency.partialSum n (half - 1)))
      else
        ideal.coClass + PowerSeries.X ^ half * PowerSeries.C
          (TauCeti.SplitK0.of alpha.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half)) +
        PowerSeries.X ^ (half + 1) * PowerSeries.C
          (TauCeti.SplitK0.of beta.cosetFDRep -
            TauCeti.SplitK0.of (Frequency.partialSum n half)) := by
  dsimp only
  by_cases heven : Even ideal.carrier.ncard
  · rw [ite_eq_left heven]
    have hcard : ideal.carrier.ncard = 2 * (ideal.carrier.ncard / 2) := by
      obtain ⟨height, hheight⟩ := heven
      omega
    have hformula := graded_class_even ideal (ideal.carrier.ncard / 2) hcard hproper
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hformula
    · rw [add_comm (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep)
        (TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep)] at hformula
      exact hformula
  · rw [ite_eq_right heven]
    have hodd := Nat.not_even_iff_odd.mp heven
    have hcard : ideal.carrier.ncard = 2 * (ideal.carrier.ncard / 2) + 1 := by
      obtain ⟨height, hheight⟩ := hodd
      omega
    exact graded_class_odd ideal _ hcard hproper alpha beta hpair (hdominant hodd)
end Right

end Schubert.DihedralSplines.HessenbergIdeal
