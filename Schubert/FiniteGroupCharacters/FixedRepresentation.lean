import Schubert.FiniteGroupCharacters.FiniteSum
import TauCeti.RepresentationTheory.CharacterTable.Determined
import Mathlib.Analysis.Complex.Basic

/-! # Finite representations whose actions fix every vector -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.FiniteGroupCharacters
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V]

/-- A fixed finite representation is a sum of its dimension of trivial objects. -/
theorem fixed_iso (source : Representation ℂ G V)
    (hfixed : ∀ element value, source element value = value) :
    Nonempty (FDRep.of source ≅
      ⨁ fun _ : Fin (Module.finrank ℂ V) => FDRep.of (Representation.trivial ℂ G ℂ)) := by
  have hsource : source = Representation.trivial ℂ G V := by
    apply MonoidHom.ext
    intro element
    apply LinearMap.ext
    intro value
    exact hfixed element value
  rw [hsource]
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [finiteSum_character]
  change (Representation.trivial ℂ G V).character element = _
  rw [Representation.char_trivial]
  simp

end Schubert.FiniteGroupCharacters
