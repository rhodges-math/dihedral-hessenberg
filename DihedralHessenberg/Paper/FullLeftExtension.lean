import DihedralHessenberg.Paper.FullLeftClass
import DihedralHessenberg.Dihedral.CosetDecomposition

/-! # The full left quotient and the odd coset expression -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral
variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- For odd n the full quotient satisfies the same coset expression. -/
theorem full_odd_class (hodd : Odd n) (alpha : PositiveRoot n) :
    RootSubset.Left.gradedClass (RootSubset.full n) hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range n,
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
      (PowerSeries.X ^ ((n - 1) / 2) + PowerSeries.X ^ ((n - 1) / 2 + 1)) *
        PowerSeries.C (TauCeti.SplitK0.of alpha.cosetFDRep -
          TauCeti.SplitK0.of (Frequency.partialSum n ((n - 1) / 2))) := by
  rw [alpha.coset_odd_class hodd, sub_self, map_zero, mul_zero, add_zero]
  exact left_class_geometric n hthree

omit [NeZero n] hthree in
/-- The even full-set half is outside the strict lower-half frequency range. -/
theorem full_even_half (heven : Even n) : ¬ 2 * (n / 2) < n := by
  obtain ⟨height, hheight⟩ := heven
  omega

end Schubert.DihedralSplines.SchubertSpline
