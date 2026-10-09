import DihedralHessenberg.Paper.RightEvenDegreeClass

/-! # The even right quotient class series -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The even right graded action has its exact coinvariant and virtual coset expression. -/
theorem graded_class_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    RootSubset.Right.gradedClass ideal.toRootSubset hthree =
      ideal.coClass +
      PowerSeries.X ^ half * PowerSeries.C
        (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
          TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
          TauCeti.SplitK0.of (Frequency.partialSum n half) -
          TauCeti.SplitK0.of (Frequency.partialSum n (half - 1))) := by
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Right.gradedClass_coeff, piece_class_even ideal half hcard hproper,
    map_add, mul_comm (PowerSeries.X ^ half),
    PowerSeries.coeff_C_mul_X_pow]

end Schubert.DihedralSplines.HessenbergIdeal.Right
