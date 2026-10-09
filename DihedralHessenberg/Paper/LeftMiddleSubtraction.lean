import DihedralHessenberg.Paper.HessenbergRemovedClass

/-! # Subtraction of the homogeneous coordinate-ideal class -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The boundary quotient class subtracts exactly the positive polynomial degrees. -/
theorem middle_subtraction (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (hpositive : 1 ≤ half) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (splineFDRep ideal half) -
        TauCeti.SplitK0.of (polynomialPieceFDRep n half) -
          2 • ∑ degree ∈ Finset.Ico 1 half,
            TauCeti.SplitK0.of (polynomialPieceFDRep n degree) := by
  rw [quotient_removed_class, removed_weighted_class ideal half hhalf hproper hpositive]
  abel

end Schubert.DihedralSplines.HessenbergIdeal.Left
