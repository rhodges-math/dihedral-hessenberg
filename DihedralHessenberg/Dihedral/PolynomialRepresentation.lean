import DihedralHessenberg.Dihedral.PolynomialGrading
import Mathlib.RepresentationTheory.Basic

/-! # The polynomial representation of the dihedral action -/

noncomputable section
namespace Schubert.Dihedral

/-- The polynomial algebra action regarded as a complex representation. -/
def polynomialRepresentation (n : ℕ) [NeZero n] :
    Representation ℂ (DihedralGroup n) CoordinatePolynomial :=
  (AlgEquiv.toLinearMapHom ℂ _).comp (polynomialAction n)

/-- The polynomial representation applies the algebra automorphism. -/
theorem polynomialRepresentation_apply (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    polynomialRepresentation n element polynomial = polynomialAction n element polynomial := rfl

end Schubert.Dihedral
