import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Intertwining

/-! # Degree restriction of representation equivalences -/

noncomputable section
namespace Schubert.FiniteGroupCharacters

/-- An equivalence carrying one stable submodule onto another restricts to their actions. -/
def restrictEquiv {K G V W : Type*} [CommRing K] [Monoid G]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {source : Representation K G V} {target : Representation K G W}
    (equivalence : Representation.Equiv source target)
    (sourcePiece : Subrepresentation source) (targetPiece : Subrepresentation target)
    (hmap : sourcePiece.toSubmodule.map equivalence.toLinearMap = targetPiece.toSubmodule) :
    Representation.Equiv sourcePiece.toRepresentation targetPiece.toRepresentation := by
  let linear := (equivalence.toLinearEquiv.submoduleMap sourcePiece.toSubmodule).trans
    (LinearEquiv.ofEq _ _ hmap)
  refine Representation.Equiv.mk linear ?_
  intro element
  apply LinearMap.ext
  intro value
  apply Subtype.ext
  change equivalence (source element value.val) = target element (equivalence value.val)
  exact equivalence.toIntertwiningMap.isIntertwining _ _ element value.val

/-- Restriction keeps the value of the representation equivalence. -/
theorem restrictEquiv_apply {K G V W : Type*} [CommRing K] [Monoid G]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {source : Representation K G V} {target : Representation K G W}
    (equivalence : Representation.Equiv source target)
    (sourcePiece : Subrepresentation source) (targetPiece : Subrepresentation target)
    (hmap : sourcePiece.toSubmodule.map equivalence.toLinearMap = targetPiece.toSubmodule)
    (value : sourcePiece.toSubmodule) :
    (restrictEquiv equivalence sourcePiece targetPiece hmap value).val = equivalence value.val :=
      rfl

end Schubert.FiniteGroupCharacters
