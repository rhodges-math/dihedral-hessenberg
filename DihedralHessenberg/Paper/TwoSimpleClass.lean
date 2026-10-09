import DihedralHessenberg.Paper.LeftEvenClass
import DihedralHessenberg.Dihedral.CosetDecomposition
import DihedralHessenberg.Dihedral.FrequencyClass
import DihedralHessenberg.Dihedral.SimpleScalar
import DihedralHessenberg.Dihedral.RootCard

/-! # The left action for the two-simple-root Hessenberg space -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Left

open Schubert.Dihedral Schubert.FiniteGroupCharacters
open scoped BigOperators

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

omit [NeZero n] in
private theorem simple_card
    (hcarrier : ideal.carrier = {(simpleRoot n hthree 0).val,
      (simpleRoot n hthree 1).val}) : ideal.carrier.ncard = 2 := by
  rw [hcarrier]
  apply Set.ncard_pair
  intro heq
  exact simpleRoot_ne n hthree (Subtype.ext heq)

omit [NeZero n] in
private theorem simple_proper
    (hcarrier : ideal.carrier = {(simpleRoot n hthree 0).val,
      (simpleRoot n hthree 1).val}) : ideal.carrier ≠ positiveRoots n := by
  intro heq
  have hcard := simple_card ideal hcarrier
  rw [heq, positiveRoots_ncard] at hcard
  omega

/-- At half-cardinality one, the two subtracted sums are the defining and two trivial terms. -/
theorem two_simple_middle :
    (TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
      TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
      TauCeti.SplitK0.of (Frequency.partialSum n 1) -
      TauCeti.SplitK0.of (Frequency.partialSum n 0) :
        TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
        TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
        TauCeti.SplitK0.of (frequencyFDRep n 1) - 2 := by
  rw [Frequency.partialSum_succ, Frequency.partialSum_zero,
    TauCeti.SplitK0.of_biprod, trivial_class_one]
  ring_nf

/-- The two-simple-root space has the degree-one virtual coset formula. -/
theorem two_simple_class
    (hcarrier : ideal.carrier = {(simpleRoot n hthree 0).val,
      (simpleRoot n hthree 1).val}) :
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      1 + PowerSeries.C
        (2 + TauCeti.SplitK0.of (simpleRoot n hthree 0).cosetFDRep +
          TauCeti.SplitK0.of (simpleRoot n hthree 1).cosetFDRep -
          TauCeti.SplitK0.of (frequencyFDRep n 1) - 2) * PowerSeries.X +
        PowerSeries.X ^ 2 := by
  rw [graded_class_even ideal 1 (by simpa using simple_card ideal hcarrier)
    (simple_proper ideal hcarrier)]
  simp only [Nat.mul_one, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add, Nat.sub_self, Frequency.partialSum_succ,
    Frequency.partialSum_zero, TauCeti.SplitK0.of_biprod, trivial_class_one]
  simp only [map_add, map_sub, map_one]
  ring_nf

/-- For odd n, the formula gives the displayed defining and doubled higher-frequency terms. -/
theorem two_simple_odd
    (hcarrier : ideal.carrier = {(simpleRoot n hthree 0).val,
      (simpleRoot n hthree 1).val}) (hodd : Odd n) :
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      1 + PowerSeries.C
        (2 + TauCeti.SplitK0.of (frequencyFDRep n 1) +
          ∑ frequency ∈ Finset.Icc 2 ((n - 1) / 2),
            2 * TauCeti.SplitK0.of (frequencyFDRep n frequency)) * PowerSeries.X +
        PowerSeries.X ^ 2 := by
  rw [two_simple_class ideal hcarrier,
    PositiveRoot.coset_odd_class _ hodd, PositiveRoot.coset_odd_class _ hodd,
    Frequency.partialSum_after_one n _ (by omega)]
  congr 2
  rw [← Finset.mul_sum]
  ring_nf

/-- For even n, the formula also retains the two even scalar constituents. -/
theorem two_simple_even
    (hcarrier : ideal.carrier = {(simpleRoot n hthree 0).val,
      (simpleRoot n hthree 1).val}) (heven : Even n) :
    RootSubset.Left.gradedClass ideal.toRootSubset hthree =
      1 + PowerSeries.C
        (2 + TauCeti.SplitK0.of (evenScalarFDRep n heven false) +
          TauCeti.SplitK0.of (evenScalarFDRep n heven true) +
          TauCeti.SplitK0.of (frequencyFDRep n 1) +
          ∑ frequency ∈ Finset.Icc 2 (n / 2 - 1),
            2 * TauCeti.SplitK0.of (frequencyFDRep n frequency)) * PowerSeries.X +
        PowerSeries.X ^ 2 := by
  have hhalf : 1 ≤ n / 2 - 1 := by
    obtain ⟨half, hhalf⟩ := heven
    omega
  rw [two_simple_class ideal hcarrier,
    PositiveRoot.coset_even_class _ heven, PositiveRoot.coset_even_class _ heven,
    first_simple_scalar, second_simple_scalar,
    Frequency.partialSum_after_one n _ hhalf]
  congr 2
  rw [← Finset.mul_sum]
  ring_nf

end Schubert.DihedralSplines.HessenbergIdeal.Left
