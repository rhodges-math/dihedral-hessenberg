import Schubert.DihedralSplines.HessenbergIdealDecomposition
import Schubert.FiniteGroupCharacters.LastWeight
import Schubert.DihedralSplines.LeftFixedRepresentation
import Schubert.Dihedral.PolynomialMultiplicity

/-! # Exact removed-ideal classes at the low-degree boundary -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A strictly low quotient degree has one or two fixed characters. -/
theorem low_piece_character (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree < half)
    (element : DihedralGroup n) :
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree).character element =
      if degree = 0 then 1 else 2 := by
  have hcharacter := FDRep.char_iso (low_piece_iso ideal half hhalf hproper degree hdegree).some
  rw [finiteSum_character] at hcharacter
  have hvalue := congrFun hcharacter element
  simpa using hvalue

/-- The removed boundary kernel has exactly the positive weighted polynomial classes. -/
theorem removed_boundary_class (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    (TauCeti.SplitK0.of (removedFDRep ideal half) : TauCeti.repRing ℂ (DihedralGroup n)) =
      ∑ split : Fin half, (if half - (split.val + 1) = 0 then 1 else 2 : ℕ) •
        TauCeti.SplitK0.of (polynomialPieceFDRep n (split.val + 1)) := by
  apply TauCeti.repRingCharacter_injective
  funext element
  simp only [map_sum, map_nsmul, TauCeti.repRingCharacter_of, Finset.sum_apply, Pi.smul_apply]
  rw [removed_piece_character]
  apply Finset.sum_congr rfl
  intro split _
  have hdegree : half - (split.val + 1) < half := by omega
  have hcharacter := low_piece_character ideal half hhalf hproper
    (half - (split.val + 1)) hdegree element
  change (polynomialPieceFDRep n (split.val + 1)).character element *
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree
      (half - (split.val + 1))).character element = _
  rw [hcharacter]
  by_cases hzero : half - (split.val + 1) = 0
  · simp [hzero]
  · simp [hzero]
    ring

/-- The removed boundary is the last polynomial degree plus twice the preceding degrees. -/
theorem removed_weighted_class (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 1 ≤ half) :
    (TauCeti.SplitK0.of (removedFDRep ideal half) : TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (polynomialPieceFDRep n half) +
        2 • ∑ degree ∈ Finset.Ico 1 half, TauCeti.SplitK0.of (polynomialPieceFDRep n degree) := by
  rw [removed_boundary_class ideal half hhalf hproper]
  exact positive_weight_sum (fun degree => TauCeti.SplitK0.of (polynomialPieceFDRep n degree))
    half hpositive

/-- The removed kernel has the exact weighted trivial and positive frequency classes. -/
theorem removed_frequency_class (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 1 ≤ half) :
    (TauCeti.SplitK0.of (removedFDRep ideal half) : TauCeti.repRing ℂ (DihedralGroup n)) =
      (half - 1) • TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
        ∑ frequency ∈ Finset.Icc 1 half,
          (half + 1 - frequency) • TauCeti.SplitK0.of (frequencyFDRep n (frequency : ℕ)) := by
  rw [removed_weighted_class ideal half hhalf hproper hpositive]
  exact polynomial_weighted_class n half hpositive

end Schubert.DihedralSplines.HessenbergIdeal.Left
