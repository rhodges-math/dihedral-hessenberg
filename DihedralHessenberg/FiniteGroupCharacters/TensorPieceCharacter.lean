import DihedralHessenberg.FiniteGroupCharacters.TensorDegreeAction
import DihedralHessenberg.FiniteGroupCharacters.DirectSumCharacter

/-! # Character convolution from homogeneous tensor equivalences -/

noncomputable section
open scoped BigOperators TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- The tensor degree character is the convolution of its factor characters. -/
theorem tensor_piece_character {K P Q I G : Type*} [Field K] [Finite P] [Finite I] [Monoid G]
    [AddCommGroup Q] [Module K Q] (scalarAction : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalarAction element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree vector, vector ∈ pieces degree → source element vector ∈ pieces
      degree)
    (degree : ℕ) (element : G) :
    letI : AddCommGroup (tensorPiece (P := P) pieces degree) := Submodule.addCommGroup _
    letI : Module K (tensorPiece (P := P) pieces degree) := Submodule.module _
    (tensorPieceRepresentation scalarAction source pieces hscalar hsource degree).character
      element =
      ∑ split : Fin (degree + 1),
        (scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K split.val)
          (fun element polynomial hpoly => hscalar element split.val polynomial hpoly)).character
          element *
        (source.subrepresentation (pieces (degree - split.val))
          (fun element vector hvector => hsource element (degree - split.val) vector
            hvector)).character
          element := by
  classical
  let family (split : Fin (degree + 1)) :=
    MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)
  let : ∀ split, AddCommGroup (family split) := fun split => inferInstance
  let : ∀ split, Module K (family split) := fun split => inferInstance
  let : AddCommGroup (⨁ split : Fin (degree + 1), family split) := inferInstance
  let : Module K (⨁ split : Fin (degree + 1), family split) := inferInstance
  let : AddCommGroup (tensorPiece (P := P) pieces degree) := Submodule.addCommGroup _
  let : Module K (tensorPiece (P := P) pieces degree) := Submodule.module _
  let : Module.Finite K Q := Module.Finite.of_basis basis
  let : ∀ split, Module.Finite K (family split) := fun split => inferInstance
  obtain ⟨equivalence⟩ := tensor_degree_equiv scalarAction source pieces basis weights hbasis
    hscalar hsource degree
  rw [← congrFun (Representation.char_iso
    (V := ⨁ split : Fin (degree + 1), family split)
    (W := tensorPiece (P := P) pieces degree) equivalence) element, directSum_character]
  apply Finset.sum_congr rfl
  intro split _
  exact congrFun (Representation.char_tensor _ _) element

end Schubert.FiniteGroupCharacters
