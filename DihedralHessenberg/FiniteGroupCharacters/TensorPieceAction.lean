import DihedralHessenberg.FiniteGroupCharacters.TensorPieceFinite
import Mathlib.RepresentationTheory.Intertwining

/-! # Diagonal actions on ordinary tensor homogeneous components -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters

variable {K P Q G : Type*} [CommRing K] [AddCommGroup Q] [Module K Q] [Monoid G]

/-- Degree-preserving factor actions preserve each ordinary total tensor degree. -/
theorem tensor_piece_stable (scalarAction : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalarAction element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree vector, vector ∈ pieces degree → source element vector ∈ pieces
      degree)
    (element : G) (degree : ℕ) (value : MvPolynomial P K ⊗[K] Q)
    (hvalue : value ∈ tensorPiece pieces degree) :
    Representation.tprod scalarAction source element value ∈ tensorPiece pieces degree := by
  induction hvalue using Submodule.span_induction with
  | mem value hvalue =>
      obtain ⟨scalarDegree, valueDegree, polynomial, vector, hdegree, hpoly, hvector, rfl⟩ := hvalue
      rw [Representation.tprod_apply, TensorProduct.map_tmul]
      exact Submodule.subset_span ⟨scalarDegree, valueDegree, scalarAction element polynomial,
        source element vector, hdegree, hscalar _ _ _ hpoly, hsource _ _ _ hvector, rfl⟩
  | zero => simp
  | add value other _ _ hvalue hother =>
      simpa only [map_add] using Submodule.add_mem _ hvalue hother
  | smul scalar value _ hvalue =>
      simpa only [map_smul] using Submodule.smul_mem _ scalar hvalue

/-- The diagonal tensor action restricted to its total-degree submodule. -/
def tensorPieceRepresentation (scalarAction : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalarAction element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree vector, vector ∈ pieces degree → source element vector ∈ pieces
      degree)
    (degree : ℕ) : Representation K G (tensorPiece (P := P) pieces degree) :=
  (Representation.tprod scalarAction source).subrepresentation (tensorPiece pieces degree)
    (fun element value hvalue => tensor_piece_stable scalarAction source pieces hscalar hsource
      element degree value hvalue)

end Schubert.FiniteGroupCharacters
