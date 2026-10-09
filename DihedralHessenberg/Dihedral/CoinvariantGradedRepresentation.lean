import DihedralHessenberg.Dihedral.CoinvariantAction
import DihedralHessenberg.Dihedral.CoinvariantHomogeneousBasis
import DihedralHessenberg.FiniteGroupCharacters.GradedCharacter
import Mathlib.RepresentationTheory.Subrepresentation

/-! # The graded coinvariant representation

The descended polynomial operators preserve every quotient degree piece. Restriction
and standard finite-dimensional bundling assemble the graded representation family.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Every coinvariant operator preserves the image of each polynomial degree piece. -/
theorem coinvariantRepresentation_mem_piece (n : ℕ) [NeZero n] (degree : ℕ)
    (element : DihedralGroup n) (value : CoinvariantAlgebra n)
    (hvalue : value ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :
    coinvariantRepresentation n element value ∈ TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree := by
  obtain ⟨polynomial, hpolynomial, rfl⟩ := (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).mp
    hvalue
  rw [coinvariantRepresentation_mk]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
    (polynomialAction_isHomogeneous n element hpolynomial)

/-- The standard restriction of the coinvariant representation to one degree piece. -/
def coinvariantPieceRepresentation (n : ℕ) [NeZero n] (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :=
  ({ toSubmodule := TauCeti.GradedAlgebra.quotientPiece
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree
     apply_mem_toSubmodule := fun element {value} hvalue =>
       coinvariantRepresentation_mem_piece n degree element value hvalue } :
    Subrepresentation (coinvariantRepresentation n)).toRepresentation

/-- Restricting to a piece leaves the underlying coinvariant vector operator unchanged. -/
theorem coinvariantPieceRepresentation_apply_coe (n : ℕ) [NeZero n] (degree : ℕ)
    (element : DihedralGroup n) (value : TauCeti.GradedAlgebra.quotientPiece
      (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) degree) :
    (coinvariantPieceRepresentation n degree element value : CoinvariantAlgebra n) =
      coinvariantRepresentation n element value := rfl

/-- The finite-dimensional bundled representation on a coinvariant degree piece. -/
def coinvariantPieceFDRep (n : ℕ) [NeZero n] (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let := coinvariant_homogeneousPiece_finite n degree
  exact FDRep.of (coinvariantPieceRepresentation n degree)

/-- The natural-number family of coinvariant degree representations. -/
def coinvariantGradedRepresentation (n : ℕ) [NeZero n] :
    Schubert.FiniteGroupCharacters.GradedRepresentation ℂ (DihedralGroup n) :=
  coinvariantPieceFDRep n

/-- The degree character is the trace of the restricted coinvariant operator. -/
theorem coinvariantPieceFDRep_character (n : ℕ) [NeZero n] (degree : ℕ)
    (element : DihedralGroup n) :
    (coinvariantPieceFDRep n degree).character element =
      (coinvariantPieceRepresentation n degree).character element := by
  let := coinvariant_homogeneousPiece_finite n degree
  exact congrFun (FDRep.character_of _) element

/-- The bundled degree representation has the existing coinvariant homogeneous-piece dimension. -/
theorem coinvariantPieceFDRep_finrank (n : ℕ) [NeZero n] (degree : ℕ) :
    Module.finrank ℂ (coinvariantPieceFDRep n degree) = Module.finrank ℂ
      (TauCeti.GradedAlgebra.quotientPiece (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ)
        (coinvariantIdeal n) degree) := rfl

end Schubert.Dihedral
