import DihedralHessenberg.Paper.LeftOddDegreeClass
import DihedralHessenberg.FiniteGroupCharacters.GeometricSeries

/-! # The odd left quotient class series -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The odd left graded action has the displayed dominant-root coset expression. -/
theorem graded_class_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hdominant : ideal.IsDominant alpha) :
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (2 * half + 1),
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
      (PowerSeries.X ^ half + PowerSeries.X ^ (half + 1)) * PowerSeries.C
        (TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half)) :=
  by
  let correction : TauCeti.repRing ℂ (DihedralGroup n) :=
    TauCeti.SplitK0.of alpha.cosetFDRep - TauCeti.SplitK0.of (Frequency.partialSum n half)
  have hcoeff (degree : ℕ) : PowerSeries.coeff degree
      ((PowerSeries.X ^ half + PowerSeries.X ^ (half + 1)) * PowerSeries.C correction) =
      if degree = half ∨ degree = half + 1 then correction else 0 := by
    rw [add_mul, map_add, mul_comm (PowerSeries.X ^ half), PowerSeries.coeff_C_mul_X_pow,
      mul_comm (PowerSeries.X ^ (half + 1)), PowerSeries.coeff_C_mul_X_pow]
    split_ifs <;> try simp
    all_goals omega
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Left.gradedClass_coeff, piece_class_odd ideal half hcard hproper alpha hdominant,
    map_add, geometric_double_coeff (2 * half + 1) degree (by omega), hcoeff]

end Schubert.DihedralSplines.HessenbergIdeal.Left
