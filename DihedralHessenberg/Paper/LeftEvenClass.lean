import DihedralHessenberg.Paper.LeftEvenDegreeClass
import DihedralHessenberg.FiniteGroupCharacters.GeometricSeries

/-! # The even left quotient class series -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The even left graded action has its exact geometric and virtual coset expression. -/
theorem graded_class_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half),
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
      PowerSeries.X ^ half * PowerSeries.C
        (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
          TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
          TauCeti.SplitK0.of (Frequency.partialSum n half) -
          TauCeti.SplitK0.of (Frequency.partialSum n (half - 1))) := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Left.gradedClass_coeff, piece_class_even ideal half hcard hproper,
    map_add, geometric_double_coeff (2 * half) degree (by omega), mul_comm (PowerSeries.X ^ half),
    PowerSeries.coeff_C_mul_X_pow]

end Schubert.DihedralSplines.HessenbergIdeal.Left
