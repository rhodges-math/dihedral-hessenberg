import DihedralHessenberg.Paper.FullCoinvariantEquivalence
import DihedralHessenberg.Dihedral.CoinvariantGradedClass

/-! # Full right quotient classes and coinvariant degrees -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral
variable (n : ℕ) [NeZero n] (hthree : 3 ≤ n)

/-- Every full right degree is the coinvariant degree with its action. -/
theorem right_piece_iso (degree : ℕ) :
    Nonempty (RootSubset.Right.pieceFDRep (RootSubset.full n) hthree degree ≅
      coinvariantPieceFDRep n degree) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨(fullCoinvariantPieceEquiv n hthree degree).symm⟩

/-- The full right graded class is the coinvariant graded class. -/
theorem right_class_coinvariant :
    RootSubset.Right.gradedClass (RootSubset.full n) hthree = Coinvariant.gradedClass n := by
  apply PowerSeries.ext
  intro degree
  rw [RootSubset.Right.gradedClass_coeff, Coinvariant.gradedClass,
    Schubert.FiniteGroupCharacters.gradedClass_coeff]
  exact TauCeti.SplitK0.of_congr (right_piece_iso n hthree degree).some

/-- Every full right coefficient is its exact trivial, frequency, sign, or zero class. -/
theorem right_class_coeff (degree : ℕ) :
    PowerSeries.coeff degree (RootSubset.Right.gradedClass (RootSubset.full n) hthree) =
      if degree = 0 then
        (TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) :
          TauCeti.repRing ℂ (DihedralGroup n))
      else if degree = n then TauCeti.SplitK0.of (signFDRep n)
      else if degree < n then TauCeti.SplitK0.of (frequencyFDRep n degree)
      else 0 := by
  rw [right_class_coinvariant, Coinvariant.gradedClass_coeff n hthree]

/-- Full right traces equal the coinvariant degree traces. -/
theorem right_character_degree (degree : ℕ) (element : DihedralGroup n) :
    (RootSubset.Right.pieceRepresentation (RootSubset.full n) hthree degree).character element =
      (coinvariantPieceRepresentation n degree).character element := by
  have h := congrFun (FDRep.char_iso (right_piece_iso n hthree degree).some) element
  simpa only [RootSubset.Right.pieceFDRep_character, coinvariantPieceFDRep_character] using h

end Schubert.DihedralSplines.SchubertSpline
