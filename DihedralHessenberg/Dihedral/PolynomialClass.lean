import DihedralHessenberg.Dihedral.PolynomialDecomposition
import DihedralHessenberg.FiniteGroupCharacters.GradedClass

/-! # Graded representation classes of binary polynomials -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace Schubert.Dihedral

/-- The degree family of the polynomial substitution action. -/
def polynomialGradedRepresentation (n : ℕ) [NeZero n] :
    Schubert.FiniteGroupCharacters.GradedRepresentation ℂ (DihedralGroup n) :=
  polynomialPieceFDRep n

/-- The formal series of polynomial degree classes in the representation ring. -/
def polynomialGradedClass (n : ℕ) [NeZero n] :
    PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
  Schubert.FiniteGroupCharacters.gradedClass (polynomialGradedRepresentation n)

/-- Each coefficient is the class of the polynomial degree representation. -/
theorem polynomialGradedClass_coeff (n : ℕ) [NeZero n] (degree : ℕ) :
    PowerSeries.coeff degree (polynomialGradedClass n) =
      TauCeti.SplitK0.of (polynomialPieceFDRep n degree) :=
  Schubert.FiniteGroupCharacters.gradedClass_coeff _ _

/-- The frequency decomposition gives the representation-ring coefficient. -/
theorem polynomialGradedClass_frequencies (n : ℕ) [NeZero n] (degree : ℕ) :
    PowerSeries.coeff degree (polynomialGradedClass n) =
      (∑ index : Fin ((degree + 1) / 2),
        TauCeti.SplitK0.of (frequencyFDRep n (degree - 2 * index.val : ℕ))) +
      if Even degree then
        TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) else 0 := by
  classical
  rw [polynomialGradedClass_coeff]
  obtain ⟨equivalence⟩ := polynomialPiece_frequency_iso n degree
  rw [TauCeti.SplitK0.of_congr equivalence, TauCeti.SplitK0.of_biprod,
    TauCeti.SplitK0.of_biproduct, TauCeti.SplitK0.of_biproduct]
  congr 1
  by_cases heven : Even degree <;> simp [heven]

end Schubert.Dihedral
