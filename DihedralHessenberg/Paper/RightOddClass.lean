import DihedralHessenberg.Paper.RightOddDegreeClass

/-! # The odd right quotient class series -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The odd right action has the dominant and opposite coset complements. -/
theorem graded_class_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (hdominant : ideal.IsDominant alpha) :
    RootSubset.Right.gradedClass ideal.toRootSubset hthree =
      ideal.coClass + PowerSeries.X ^ half * PowerSeries.C
        (TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half)) +
      PowerSeries.X ^ (half + 1) * PowerSeries.C
        (TauCeti.SplitK0.of beta.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half)) :=
  by
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Right.gradedClass_coeff,
    piece_class_odd ideal half hcard hproper alpha beta hpair hdominant,
    map_add, map_add, mul_comm (PowerSeries.X ^ half), PowerSeries.coeff_C_mul_X_pow,
    mul_comm (PowerSeries.X ^ (half + 1)), PowerSeries.coeff_C_mul_X_pow]

end Schubert.DihedralSplines.HessenbergIdeal.Right
