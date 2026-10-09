import DihedralHessenberg.Paper.MissingTopIdeal
import DihedralHessenberg.Paper.LeftEvenClass
import DihedralHessenberg.Paper.LeftOddClass
import DihedralHessenberg.Dihedral.CosetDecomposition

/-! # Classes of quotients omitting the final root -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral
variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- For even n the omitted-root correction is its dominant scalar character. -/
theorem withoutLast_class_even (heven : Even n) (alpha : PositiveRoot n)
    (hdominant : (withoutLast n hthree).IsDominant alpha) :
    RootSubset.Left.gradedClass (withoutLast n hthree).toRootSubset hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (n - 1),
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
      (PowerSeries.X ^ (n / 2 - 1) + PowerSeries.X ^ (n / 2)) *
        PowerSeries.C (TauCeti.SplitK0.of (alpha.scalarFDRep heven)) := by
  have hhalf : n / 2 - 1 + 1 = n / 2 := by
    have hmod := Nat.even_iff.mp heven
    omega
  have hformula := graded_class_odd (withoutLast n hthree) (n / 2 - 1)
    (withoutLast_even n hthree heven) (withoutLast_proper n hthree) alpha hdominant
  rw [alpha.coset_even_class heven] at hformula
  have hsize : 2 * (n / 2 - 1) + 1 = n - 1 :=
    (withoutLast_even n hthree heven).symm.trans (withoutLast_card n hthree)
  simpa only [hsize, hhalf, add_sub_cancel_right] using hformula

/-- For odd n the omitted-root correction is the last lower-half frequency. -/
theorem withoutLast_class_odd (hodd : Odd n) :
    RootSubset.Left.gradedClass (withoutLast n hthree).toRootSubset hthree =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range (n - 1),
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent +
      PowerSeries.X ^ ((n - 1) / 2) *
        PowerSeries.C (TauCeti.SplitK0.of (frequencyFDRep n ((n - 1) / 2 : ℕ))) := by
  have hformula := graded_class_even (withoutLast n hthree) ((n - 1) / 2)
    (withoutLast_odd n hthree hodd) (withoutLast_proper n hthree)
  rw [(simpleRoot n hthree 0).coset_odd_class hodd,
    (simpleRoot n hthree 1).coset_odd_class hodd] at hformula
  have hsize : 2 * ((n - 1) / 2) = n - 1 :=
    (withoutLast_odd n hthree hodd).symm.trans (withoutLast_card n hthree)
  have hhalf : (n - 1) / 2 - 1 + 1 = (n - 1) / 2 := by omega
  have hprefix : (TauCeti.SplitK0.of (Frequency.partialSum n ((n - 1) / 2)) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (Frequency.partialSum n ((n - 1) / 2 - 1)) +
      TauCeti.SplitK0.of (frequencyFDRep n ((n - 1) / 2 : ℕ)) := by
    conv_lhs => rw [← hhalf, Frequency.partialSum_succ, TauCeti.SplitK0.of_biprod]
    rw [hhalf]
  rw [hsize] at hformula
  convert hformula using 1
  congr 2
  rw [hprefix]
  abel_nf

end Schubert.DihedralSplines.HessenbergIdeal.Left
