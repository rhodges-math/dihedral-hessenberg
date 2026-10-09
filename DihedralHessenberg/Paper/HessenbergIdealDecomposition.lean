import DihedralHessenberg.Paper.HessenbergIdealConvolution
import DihedralHessenberg.FiniteGroupCharacters.EquivariantSplit

/-! # Coordinate-kernel decompositions of spline degree representations -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The removed kernel degree is a biproduct of positive tensor factors. -/
theorem removed_degree_iso (degree : ℕ) : Nonempty (removedFDRep ideal degree ≅
    ⨁ fun split : Fin degree => polynomialPieceFDRep n (split.val + 1) ⊗
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree (degree - (split.val + 1))) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [finiteSum_character, removed_piece_character]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  rw [FDRep.char_tensor, Pi.mul_apply]
  simp only [RootSubset.Left.pieceFDRep_character]
  rfl

/-- Each quotient degree class subtracts its removed coordinate kernel. -/
theorem quotient_removed_class (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (splineFDRep ideal degree) -
        TauCeti.SplitK0.of (removedFDRep ideal degree) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  exact quotient_class (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree) (by
    intro value
    obtain ⟨original, horiginal, hmap⟩ :=
      (RootSubset.Left.mem_piece ideal.toRootSubset hthree degree value.val).1 value.property
    exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩)

end Left


namespace Right

/-- The removed kernel degree is a biproduct of positive tensor factors. -/
theorem removed_degree_iso (degree : ℕ) : Nonempty (removedFDRep ideal degree ≅
    ⨁ fun split : Fin degree => trivialPolynomialPiece n (split.val + 1) ⊗
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree (degree - (split.val + 1))) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [finiteSum_character, removed_piece_character]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  rw [FDRep.char_tensor, Pi.mul_apply]
  simp only [RootSubset.Right.pieceFDRep_character]
  rfl

/-- Each quotient degree class subtracts its removed coordinate kernel. -/
theorem quotient_removed_class (degree : ℕ) :
    (TauCeti.SplitK0.of (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
      TauCeti.SplitK0.of (splineFDRep ideal degree) -
        TauCeti.SplitK0.of (removedFDRep ideal degree) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  exact quotient_class (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree) (by
    intro value
    obtain ⟨original, horiginal, hmap⟩ :=
      (RootSubset.Right.mem_piece ideal.toRootSubset hthree degree value.val).1 value.property
    exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩)

end Right

end Schubert.DihedralSplines.HessenbergIdeal
