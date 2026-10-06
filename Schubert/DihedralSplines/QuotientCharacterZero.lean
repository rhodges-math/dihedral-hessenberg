import TauCeti.RepresentationTheory.CharacterTable.Determined
import Schubert.DihedralSplines.PieceFinite
import Mathlib.LinearAlgebra.Dimension.Finite
import Schubert.FiniteGroupCharacters.ReflectionQuotientNontrivial
import Schubert.DihedralSplines.DegreeZero
import Mathlib.RepresentationTheory.Character

/-! # Degree-zero characters of the two Hessenberg quotients

Both quotients retain the unit, and their degree-zero pieces consist of its scalar multiples.
Their dot representations therefore have dimension and character one in degree zero.
-/

noncomputable section

open CategoryTheory

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergSpace n hthree)

/-- The left Hessenberg quotient retains a nonzero unit. -/
theorem leftHessenbergQuotient_nontrivial : Nontrivial (LeftHessenbergQuotient ideal) :=
  (dihedralReflectionData n hthree).leftQuotient_nontrivial
    (ideal.roots : Set (PositiveRootIndex n))

/-- The left quotient has one-dimensional degree-zero piece. -/
theorem leftHessenbergQuotientPiece_zero_finrank :
    Module.finrank ℂ (leftHessenbergQuotientPiece ideal 0) = 1 := by
  let := leftHessenbergQuotient_nontrivial ideal
  let := leftHessenbergQuotientGradedAlgebra ideal
  let unit : leftHessenbergQuotientPiece ideal 0 := ⟨1, SetLike.GradedOne.one_mem⟩
  apply finrank_eq_one unit
  · intro hzero
    exact one_ne_zero (congrArg Subtype.val hzero)
  · intro value
    obtain ⟨scalar, hscalar⟩ :=
      _root_.Schubert.DihedralSplines.IndexedSpline.Left.Quotient.degree_zero_eq_scalar
      ideal value.val value.property
    refine ⟨scalar, ?_⟩
    apply Subtype.ext
    change scalar • (1 : LeftHessenbergQuotient ideal) = value.val
    rw [hscalar]
    exact (Algebra.algebraMap_eq_smul_one scalar).symm

/-- The left quotient degree-zero character is the trivial character. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.zero_character (element :
  DihedralGroup n) :
    (_root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation ideal 0).character
      element = 1 := by
  let := leftHessenbergQuotientPiece_finite ideal 0
  have hidentity : _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation ideal 0
    element = LinearMap.id := by
    apply LinearMap.ext
    intro value
    exact _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation_zero_apply ideal
      element value
  rw [Representation.character, hidentity, LinearMap.trace_id,
    leftHessenbergQuotientPiece_zero_finrank]
  norm_num

/-- The right Hessenberg quotient retains a nonzero unit. -/
theorem rightHessenbergQuotient_nontrivial : Nontrivial (RightHessenbergQuotient ideal) :=
  (dihedralReflectionData n hthree).rightQuotient_nontrivial
    (ideal.roots : Set (PositiveRootIndex n))

/-- The right quotient has one-dimensional degree-zero piece. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.zero_finrank :
    Module.finrank ℂ (rightHessenbergQuotientPiece ideal 0) = 1 := by
  let := rightHessenbergQuotient_nontrivial ideal
  let := rightHessenbergQuotientGradedAlgebra ideal
  let unit : rightHessenbergQuotientPiece ideal 0 := ⟨1, SetLike.GradedOne.one_mem⟩
  apply finrank_eq_one unit
  · intro hzero
    exact one_ne_zero (congrArg Subtype.val hzero)
  · intro value
    obtain ⟨scalar, hscalar⟩ :=
      _root_.Schubert.DihedralSplines.IndexedSpline.Right.Quotient.degree_zero_eq_scalar
      ideal value.val value.property
    refine ⟨scalar, ?_⟩
    apply Subtype.ext
    change scalar • (1 : RightHessenbergQuotient ideal) = value.val
    rw [hscalar]
    exact (Algebra.algebraMap_eq_smul_one scalar).symm

/-- The right quotient degree-zero character is the trivial character. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.zero_character (element :
  DihedralGroup n) :
    (_root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation ideal 0).character
      element = 1 := by
  let := rightHessenbergQuotientPiece_finite ideal 0
  have hidentity : _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation ideal 0
    element = LinearMap.id := by
    apply LinearMap.ext
    intro value
    exact _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation_zero_apply ideal
      element value
  rw [Representation.character, hidentity, LinearMap.trace_id,
    _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.zero_finrank]
  norm_num

/-- The left degree-zero quotient representation is isomorphic to the trivial representation. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.zero_iso_trivial :
    letI := leftHessenbergQuotientPiece_finite ideal 0
    Nonempty (FDRep.of (_root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.Representation
      ideal 0) ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  let := leftHessenbergQuotientPiece_finite ideal 0
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.character_of_trivial, FDRep.character_of]
  exact _root_.Schubert.DihedralSplines.IndexedSpline.Left.Piece.zero_character ideal element

/-- The right degree-zero quotient representation is isomorphic to the trivial representation. -/
theorem _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.zero_iso_trivial :
    letI := rightHessenbergQuotientPiece_finite ideal 0
    Nonempty (FDRep.of (_root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.Representation
      ideal 0) ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  let := rightHessenbergQuotientPiece_finite ideal 0
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.character_of_trivial, FDRep.character_of]
  exact _root_.Schubert.DihedralSplines.IndexedSpline.Right.Piece.zero_character ideal element
end Schubert.DihedralSplines






