import DihedralHessenberg.FiniteGroupCharacters.PositiveTensorDegree
import DihedralHessenberg.FiniteGroupCharacters.PositiveTensorAction

/-! # Equivariant degree decomposition of positive scalar tensors -/

noncomputable section
open scoped TensorProduct DirectSum
namespace Schubert.FiniteGroupCharacters

/-- Degree splitting intertwines the factor actions and the tensor action. -/
theorem positive_tensor_degree_equiv {K P Q I G : Type*} [Field K] [Finite P] [Finite I] [Monoid G]
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
    (degree : ℕ) :
    Nonempty (Representation.Equiv
      (Representation.directSum fun split : Fin degree =>
        Representation.tprod
          (scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K (split.val + 1))
            (fun element polynomial hpoly => hscalar element (split.val + 1) polynomial hpoly))
          (source.subrepresentation (pieces (degree - (split.val + 1)))
            (fun element vector hvector =>
              hsource element (degree - (split.val + 1)) vector hvector)))
      (positiveTensorPieceRepresentation scalarAction source pieces basis hconstant hscalar hsource
        degree)) := by
  classical
  let scalarPieces (split : Fin degree) :=
    scalarAction.subrepresentation (MvPolynomial.homogeneousSubmodule P K (split.val + 1))
      (fun element polynomial hpoly => hscalar element (split.val + 1) polynomial hpoly)
  let sourcePieces (split : Fin degree) :=
    source.subrepresentation (pieces (degree - (split.val + 1)))
      (fun element vector hvector => hsource element (degree - (split.val + 1)) vector hvector)
  let actions (split : Fin degree) := Representation.tprod (scalarPieces split)
    (sourcePieces split)
  let family (split : Fin degree) :=
    MvPolynomial.homogeneousSubmodule P K (split.val + 1) ⊗[K] pieces (degree - (split.val + 1))
  refine ⟨Representation.Equiv.mk
    (positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm ?_⟩
  intro element
  apply DirectSum.linearMap_ext
  intro split
  apply TensorProduct.ext'
  intro polynomial vector
  apply Subtype.ext
  change ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.lmap (fun split => actions split element)
      (DirectSum.lof K (Fin degree) family split (polynomial ⊗ₜ[K] vector)))).val =
    (Representation.tprod scalarAction source) element
      ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
        (DirectSum.lof K (Fin degree) family split (polynomial ⊗ₜ[K] vector))).val
  rw [DirectSum.lmap_lof]
  change ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
    (DirectSum.of family split
      (Representation.tprod (scalarPieces split) (sourcePieces split) element
        (polynomial ⊗ₜ[K] vector)))).val =
    (Representation.tprod scalarAction source) element
      ((positiveTensorDegreeEquiv pieces basis weights hbasis degree).symm
        (DirectSum.of family split (polynomial ⊗ₜ[K] vector))).val
  rw [Representation.tprod_apply, TensorProduct.map_tmul, positiveTensorDegreeEquiv_symm_tmul,
    positiveTensorDegreeEquiv_symm_tmul, Representation.tprod_apply, TensorProduct.map_tmul]
  rfl

end Schubert.FiniteGroupCharacters
