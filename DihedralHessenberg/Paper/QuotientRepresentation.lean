import DihedralHessenberg.Paper.PaperQuotientAction
import DihedralHessenberg.Paper.PaperQuotientFinite
import DihedralHessenberg.FiniteGroupCharacters.GradedClass

/-! # Graded representation classes of geometric spline quotients -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- The standard finite-dimensional object of the geometric quotient degree action. -/
def pieceFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let := quotient_finite selected hthree
  exact FDRep.of (pieceRepresentation selected hthree degree)

/-- The natural degree family of the geometric quotient actions. -/
def gradedRepresentation :
    Schubert.FiniteGroupCharacters.GradedRepresentation ℂ (DihedralGroup n) :=
  pieceFDRep selected hthree

/-- The formal series of the quotient degree classes in the representation ring. -/
def gradedClass : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
  Schubert.FiniteGroupCharacters.gradedClass (gradedRepresentation selected hthree)

/-- Bundling a quotient degree action preserves its trace character. -/
theorem pieceFDRep_character (degree : ℕ) (element : DihedralGroup n) :
    (pieceFDRep selected hthree degree).character element =
      (pieceRepresentation selected hthree degree).character element := by
  let := quotient_finite selected hthree
  exact congrFun (FDRep.character_of _) element

/-- The degree object has the dimension of its geometric quotient piece. -/
theorem pieceFDRep_finrank (degree : ℕ) :
    Module.finrank ℂ (pieceFDRep selected hthree degree) =
      Module.finrank ℂ (piece selected hthree degree) := rfl

/-- The coefficient of the quotient series is the class of the degree action. -/
theorem gradedClass_coeff (degree : ℕ) :
    PowerSeries.coeff degree (gradedClass selected hthree) =
      TauCeti.SplitK0.of (pieceFDRep selected hthree degree) :=
  Schubert.FiniteGroupCharacters.gradedClass_coeff _ _

end Left

namespace Right

/-- The standard finite-dimensional object of the geometric quotient degree action. -/
def pieceFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let := quotient_finite selected hthree
  exact FDRep.of (pieceRepresentation selected hthree degree)

/-- The natural degree family of the geometric quotient actions. -/
def gradedRepresentation :
    Schubert.FiniteGroupCharacters.GradedRepresentation ℂ (DihedralGroup n) :=
  pieceFDRep selected hthree

/-- The formal series of the quotient degree classes in the representation ring. -/
def gradedClass : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
  Schubert.FiniteGroupCharacters.gradedClass (gradedRepresentation selected hthree)

/-- Bundling a quotient degree action preserves its trace character. -/
theorem pieceFDRep_character (degree : ℕ) (element : DihedralGroup n) :
    (pieceFDRep selected hthree degree).character element =
      (pieceRepresentation selected hthree degree).character element := by
  let := quotient_finite selected hthree
  exact congrFun (FDRep.character_of _) element

/-- The degree object has the dimension of its geometric quotient piece. -/
theorem pieceFDRep_finrank (degree : ℕ) :
    Module.finrank ℂ (pieceFDRep selected hthree degree) =
      Module.finrank ℂ (piece selected hthree degree) := rfl

/-- The coefficient of the quotient series is the class of the degree action. -/
theorem gradedClass_coeff (degree : ℕ) :
    PowerSeries.coeff degree (gradedClass selected hthree) =
      TauCeti.SplitK0.of (pieceFDRep selected hthree degree) :=
  Schubert.FiniteGroupCharacters.gradedClass_coeff _ _

end Right

end Schubert.Dihedral.RootSubset
