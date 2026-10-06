import Schubert.FiniteGroupCharacters.PositiveTensorDegreeAction
import Schubert.FiniteGroupCharacters.DirectSumCharacter

/-! # Character convolution for positive scalar tensor degrees -/

noncomputable section
open scoped BigOperators TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- The tensor degree character is the convolution of its factor characters. -/
theorem positive_tensor_piece_character {K P Q I G : Type*} [Field K] [Finite P] [Finite I]
    [Monoid G]
    [AddCommGroup Q] [Module K Q] (scalarAction : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hconstant : ∀ element polynomial, (scalarAction element polynomial).constantCoeff =
      polynomial.constantCoeff)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalarAction element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree vector, vector ∈ pieces degree → source element vector ∈ pieces
      degree)
    (degree : ℕ) (element : G) :
    letI : AddCommGroup ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) :=
      Submodule.addCommGroup _
    letI : Module K ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) :=
      Submodule.module _
    (positiveTensorPieceRepresentation scalarAction source pieces basis hconstant hscalar hsource
      degree).character
      element =
      ∑ split : Fin degree,
        (scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K (split.val + 1))
          (fun element polynomial hpoly =>
            hscalar element (split.val + 1) polynomial hpoly)).character
          element *
        (source.subrepresentation (pieces (degree - (split.val + 1)))
          (fun element vector hvector => hsource element (degree - (split.val + 1)) vector
            hvector)).character
          element := by
  classical
  let family (split : Fin degree) :=
    MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K] pieces (degree - (split.val + 1))
  let : ∀ split, AddCommGroup (family split) := fun split => inferInstance
  let : ∀ split, Module K (family split) := fun split => inferInstance
  let : AddCommGroup (⨁ split : Fin degree, family split) := inferInstance
  let : Module K (⨁ split : Fin degree, family split) := inferInstance
  let : AddCommGroup ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) :=
    Submodule.addCommGroup _
  let : Module K ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree) :=
    Submodule.module _
  let : Module.Finite K Q := Module.Finite.of_basis basis
  let : ∀ split, Module.Finite K (family split) := fun split => inferInstance
  obtain ⟨equivalence⟩ := positive_tensor_degree_equiv scalarAction source pieces
    basis weights hbasis
    hconstant hscalar hsource degree
  rw [← congrFun (Representation.char_iso
    (V := ⨁ split : Fin degree, family split)
    (W := ↥(positiveTensor (P := P) ⊓ tensorPiece (P := P) pieces degree)) equivalence) element,
    directSum_character]
  apply Finset.sum_congr rfl
  intro split _
  exact congrFun (Representation.char_tensor _ _) element

end Schubert.FiniteGroupCharacters
