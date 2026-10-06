import Schubert.FiniteGroupCharacters.PositiveTensorAction
import Schubert.FiniteGroupCharacters.TensorAugmentationTransport
import Schubert.FiniteGroupCharacters.RestrictEquiv
import Schubert.FiniteGroupCharacters.KernelRestriction

/-! # Positive tensor equivalences to homogeneous projection kernels -/

noncomputable section
open scoped TensorProduct
namespace Schubert.FiniteGroupCharacters
variable {K P Q M I G : Type*} [Field K] [Monoid G]
variable [AddCommGroup Q] [Module K Q] [AddCommGroup M] [Module K M]

/-- A normalized graded tensor equivalence identifies the homogeneous projection kernel. -/
theorem tensor_kernel_degree_equiv (scalar : Representation K G (MvPolynomial P K))
    (source : Representation K G Q) (target : Representation K G M)
    (pieces : ℕ → Submodule K Q) (basis : Module.Basis I K Q)
    (hconstant : ∀ element polynomial, (scalar element polynomial).constantCoeff =
      polynomial.constantCoeff)
    (hscalar : ∀ element degree polynomial, polynomial.IsHomogeneous degree →
      (scalar element polynomial).IsHomogeneous degree)
    (hsource : ∀ element degree value, value ∈ pieces degree → source element value ∈ pieces degree)
    (degree : ℕ) (equivalence : Representation.Equiv (scalar.tprod source) target)
    (projection : target.IntertwiningMap source)
    (hpure : ∀ polynomial value, projection (equivalence (polynomial ⊗ₜ[K] value)) =
      polynomial.constantCoeff • value)
    (sourcePiece : Subrepresentation target) (quotientPiece : Subrepresentation source)
    (restricted : sourcePiece.toRepresentation.IntertwiningMap quotientPiece.toRepresentation)
    (happly : ∀ value, (restricted value).val = projection value.val)
    (hdegree : (tensorPiece (P := P) pieces degree).map equivalence.toLinearMap =
      sourcePiece.toSubmodule) :
    Nonempty (Representation.Equiv
      (positiveTensorPieceRepresentation scalar source pieces basis hconstant hscalar
        hsource degree)
      restricted.ker.toRepresentation) := by
  let positivePiece : Subrepresentation (scalar.tprod source) :=
    { toSubmodule := positiveTensor ⊓ tensorPiece pieces degree
      apply_mem_toSubmodule := fun element value hvalue =>
        positive_tensor_piece_stable scalar source pieces basis hconstant hscalar hsource
          element degree value hvalue }
  have hmap : positivePiece.toSubmodule.map equivalence.toLinearMap =
      (projection.ker ⊓ sourcePiece).toSubmodule :=
    positive_tensor_degree_map basis equivalence.toLinearEquiv projection.toLinearMap
      hpure (tensorPiece pieces degree) sourcePiece.toSubmodule hdegree
  exact ⟨(restrictEquiv equivalence positivePiece (projection.ker ⊓ sourcePiece) hmap).trans
    (kernelRestrictionEquiv projection sourcePiece quotientPiece restricted happly)⟩

end Schubert.FiniteGroupCharacters
