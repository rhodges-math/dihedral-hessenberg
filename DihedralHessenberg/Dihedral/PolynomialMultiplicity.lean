import DihedralHessenberg.Dihedral.PolynomialClass
import DihedralHessenberg.FiniteGroupCharacters.WeightMultiplicity

/-! # Multiplicities in weighted sums of polynomial degree classes -/

noncomputable section
open scoped BigOperators
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters

/-- The weighted polynomial degree sum has the exact positive-frequency multiplicities. -/
theorem polynomial_weighted_class (n : ℕ) [NeZero n] (height : ℕ) (hheight : 1 ≤ height) :
    (TauCeti.SplitK0.of (polynomialPieceFDRep n height) : TauCeti.repRing ℂ (DihedralGroup n)) +
      2 • (∑ degree ∈ Finset.Ico 1 height, TauCeti.SplitK0.of (polynomialPieceFDRep n degree)) =
    (height - 1) • TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) +
      ∑ frequency ∈ Finset.Icc 1 height,
        (height + 1 - frequency) • TauCeti.SplitK0.of (frequencyFDRep n (frequency : ℕ)) := by
  have hdegree : ∀ degree,
      (TauCeti.SplitK0.of (polynomialPieceFDRep n degree) : TauCeti.repRing ℂ (DihedralGroup n)) =
        weightPiece (TauCeti.SplitK0.of
          (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)))
          (fun frequency => TauCeti.SplitK0.of (frequencyFDRep n (frequency : ℕ))) degree := by
    intro degree
    rw [← polynomialGradedClass_coeff, polynomialGradedClass_frequencies]
    rfl
  simp_rw [hdegree]
  exact weightPiece_multiplicity _ _ height hheight

end Schubert.Dihedral
