import DihedralHessenberg.FiniteGroupCharacters.TensorDegreeEquiv
import DihedralHessenberg.FiniteGroupCharacters.TensorPieceAction

/-! # Equivariant degreewise decomposition of ordinary tensor products -/

noncomputable section
open scoped TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- Degree splitting intertwines the factor actions and the tensor action. -/
theorem tensor_degree_equiv {K P Q I G : Type*} [CommRing K] [Monoid G]
    [AddCommGroup Q] [Module K Q] (scalarAction : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (pieces : ℕ → Submodule K Q)
    [DirectSum.Decomposition pieces] (basis : Module.Basis I K Q) (weights : I → ℕ)
    (hbasis : ∀ index, basis index ∈ pieces (weights index))
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalarAction element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree vector, vector ∈ pieces degree → source element vector ∈ pieces
      degree)
    (degree : ℕ) :
    Nonempty (Representation.Equiv
      (Representation.directSum fun split : Fin (degree + 1) =>
        Representation.tprod
          (scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K split.val)
            (fun element polynomial hpoly => hscalar element split.val polynomial hpoly))
          (source.subrepresentation (pieces (degree - split.val))
            (fun element vector hvector => hsource element (degree - split.val) vector hvector)))
      (tensorPieceRepresentation scalarAction source pieces hscalar hsource degree)) := by
  classical
  let scalarPieces (split : Fin (degree + 1)) :=
    scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K split.val)
      (fun element polynomial hpoly => hscalar element split.val polynomial hpoly)
  let sourcePieces (split : Fin (degree + 1)) :=
    source.subrepresentation (pieces (degree - split.val))
      (fun element vector hvector => hsource element (degree - split.val) vector hvector)
  let actions (split : Fin (degree + 1)) := Representation.tprod (scalarPieces split)
    (sourcePieces split)
  let family (split : Fin (degree + 1)) :=
    MvPolynomial.homogeneousSubmodule P K split.val ⊗[K] pieces (degree - split.val)
  refine ⟨Representation.Equiv.mk (tensorDegreeEquiv pieces basis weights hbasis degree).symm ?_⟩
  intro element
  apply DirectSum.linearMap_ext
  intro split
  apply TensorProduct.ext'
  intro polynomial vector
  apply Subtype.ext
  change ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.lmap (fun split => actions split element)
      (DirectSum.lof K (Fin (degree + 1)) family split (polynomial ⊗ₜ[K] vector)))).val =
    (Representation.tprod scalarAction source) element
      ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
        (DirectSum.lof K (Fin (degree + 1)) family split (polynomial ⊗ₜ[K] vector))).val
  rw [DirectSum.lmap_lof]
  change ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.of family split
      (Representation.tprod (scalarPieces split) (sourcePieces split) element
        (polynomial ⊗ₜ[K] vector)))).val =
    (Representation.tprod scalarAction source) element
      ((tensorDegreeEquiv pieces basis weights hbasis degree).symm
        (DirectSum.of family split (polynomial ⊗ₜ[K] vector))).val
  rw [Representation.tprod_apply, TensorProduct.map_tmul, tensorDegreeEquiv_symm_tmul,
    tensorDegreeEquiv_symm_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
  rfl

end Schubert.FiniteGroupCharacters
