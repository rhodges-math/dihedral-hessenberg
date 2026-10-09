import Mathlib.RepresentationTheory.Intertwining

/-! # Perfect equivariant pairings as equivalences of representations -/

noncomputable section
namespace Schubert.FiniteGroupCharacters

/-- A perfect diagonal-equivariant pairing is an equivalence to the linear-map action. -/
def pairingActionEquiv {K G V W T : Type*} [CommRing K] [Group G]
    [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Module K V] [Module K W] [Module K T]
    (first : Representation K G V) (second : Representation K G W)
    (top : Representation K G T) (pairing : V ≃ₗ[K] (W →ₗ[K] T))
    (hpairing : ∀ element value partner,
      pairing (first element value) (second element partner) =
        top element (pairing value partner)) :
    Representation.Equiv first (Representation.linHom second top) := by
  refine Representation.Equiv.mk pairing ?_
  intro element
  apply LinearMap.ext
  intro value
  apply LinearMap.ext
  intro partner
  have hvalue := hpairing element value (second element⁻¹ partner)
  change pairing (first element value) partner =
    top element (pairing value (second element⁻¹ partner))
  rw [Representation.self_inv_apply] at hvalue
  exact hvalue

end Schubert.FiniteGroupCharacters
