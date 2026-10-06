import Schubert.Dihedral.PolynomialRepresentation
import TauCeti.RingTheory.MvPolynomial.Finrank
import Schubert.FiniteGroupCharacters.FiniteSum
import TauCeti.RepresentationTheory.RepresentationRing.Injective

/-! # Homogeneous pieces of the dihedral polynomial representation -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace Schubert.Dihedral

/-- The substitution representation restricted to one polynomial degree. -/
def polynomialPieceRepresentation (n : ℕ) [NeZero n] (degree : ℕ) :
    Representation ℂ (DihedralGroup n) (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree) :=
  (polynomialRepresentation n).subrepresentation
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree)
    (fun element _ hvalue => polynomialAction_isHomogeneous n element hvalue)

/-- The homogeneous polynomial action is a finite-dimensional representation. -/
def polynomialPieceFDRep (n : ℕ) [NeZero n] (degree : ℕ) : FDRep ℂ (DihedralGroup n) :=
  FDRep.of (polynomialPieceRepresentation n degree)

/-- The polynomial degree piece has the standard binary-form dimension. -/
theorem polynomialPieceFDRep_finrank (n : ℕ) [NeZero n] (degree : ℕ) :
    Module.finrank ℂ (polynomialPieceFDRep n degree) = degree + 1 := by
  change Module.finrank ℂ (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree) = _
  exact TauCeti.finrank_homogeneousSubmodule_fin_two ℂ degree

/-- A polynomial degree piece with the trivial coefficient action. -/
def trivialPolynomialPiece (n : ℕ) (degree : ℕ) : FDRep ℂ (DihedralGroup n) :=
  FDRep.of (Representation.trivial ℂ (DihedralGroup n)
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree))

/-- A trivial binary-form piece is a sum of degree plus one trivial objects. -/
theorem trivialPolynomialPiece_iso (n : ℕ) [NeZero n] (degree : ℕ) :
    Nonempty (trivialPolynomialPiece n degree ≅
      ⨁ fun _ : Fin (degree + 1) => FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [Schubert.FiniteGroupCharacters.finiteSum_character]
  change (Representation.trivial ℂ (DihedralGroup n)
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ degree)).character element = _
  rw [Representation.char_trivial, TauCeti.finrank_homogeneousSubmodule_fin_two]
  simp

end Schubert.Dihedral
