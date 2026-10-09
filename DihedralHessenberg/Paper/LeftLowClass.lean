import DihedralHessenberg.FiniteGroupCharacters.ClassDimension
import DihedralHessenberg.Paper.LeftFixedRepresentation

/-! # Fixed classes of lower quotient degrees -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every left quotient degree below the middle has its exact fixed class. -/
theorem low_piece_class (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree < half) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = (if degree = 0 then 1 else 2) • 1 := by
  rw [TauCeti.SplitK0.of_congr (low_piece_iso ideal half hhalf hproper degree hdegree).some,
    TauCeti.SplitK0.of_biproduct]
  simp only [trivial_class_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Schubert.DihedralSplines.HessenbergIdeal.Left
