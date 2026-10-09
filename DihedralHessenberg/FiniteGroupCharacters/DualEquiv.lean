import Mathlib.RepresentationTheory.Intertwining

/-! # Transport of dual representations along representation equivalences -/

noncomputable section
namespace Schubert.FiniteGroupCharacters

/-- A representation equivalence induces an equivalence of its dual actions. -/
def dualEquiv {K G V W : Type*} [CommRing K] [Group G]
    [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {source : Representation K G V} {target : Representation K G W}
    (equivalence : Representation.Equiv source target) :
    Representation.Equiv source.dual target.dual := by
  refine Representation.Equiv.mk equivalence.toLinearEquiv.symm.dualMap ?_
  intro element
  apply LinearMap.ext
  intro functional
  apply LinearMap.ext
  intro value
  change functional (source element⁻¹ (equivalence.symm value)) =
    functional (equivalence.symm (target element⁻¹ value))
  exact congrArg functional
    (equivalence.symm.toIntertwiningMap.isIntertwining _ _ element⁻¹ value).symm

end Schubert.FiniteGroupCharacters
