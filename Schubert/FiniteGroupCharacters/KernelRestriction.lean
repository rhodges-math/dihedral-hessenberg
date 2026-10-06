import Mathlib.RepresentationTheory.Intertwining

/-! # Kernels under homogeneous restriction -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G V W : Type*} [CommRing K] [Monoid G]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Restricting a projection identifies its kernel with the kernel intersection. -/
def kernelRestrictionEquiv {source : Representation K G V} {target : Representation K G W}
    (projection : source.IntertwiningMap target) (sourcePiece : Subrepresentation source)
    (targetPiece : Subrepresentation target)
    (restricted : sourcePiece.toRepresentation.IntertwiningMap targetPiece.toRepresentation)
    (happly : ∀ value, (restricted value).val = projection value.val) :
    Representation.Equiv (projection.ker ⊓ sourcePiece).toRepresentation
      restricted.ker.toRepresentation := by
  let linear : (projection.ker ⊓ sourcePiece).toSubmodule ≃ₗ[K]
      restricted.ker.toSubmodule :=
    { toFun := fun value => ⟨⟨value.val, value.property.2⟩, by
        apply Subtype.ext
        change (restricted ⟨value.val, value.property.2⟩).val = 0
        rw [happly]
        exact value.property.1⟩
      invFun := fun value => ⟨value.val.val, by
        constructor
        · change projection value.val.val = 0
          rw [← happly]
          exact congrArg Subtype.val value.property
        · exact value.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Representation.Equiv.mk linear ?_
  intro element
  apply LinearMap.ext
  intro value
  rfl

/-- The kernel restriction equivalence preserves the underlying vector. -/
theorem kernelRestrictionEquiv_apply {source : Representation K G V}
    {target : Representation K G W} (projection : source.IntertwiningMap target)
    (sourcePiece : Subrepresentation source) (targetPiece : Subrepresentation target)
    (restricted : sourcePiece.toRepresentation.IntertwiningMap targetPiece.toRepresentation)
    (happly : ∀ value, (restricted value).val = projection value.val)
    (value : (projection.ker ⊓ sourcePiece).toSubmodule) :
    (kernelRestrictionEquiv projection sourcePiece targetPiece restricted happly value).val.val =
      value.val := rfl

end Schubert.FiniteGroupCharacters
