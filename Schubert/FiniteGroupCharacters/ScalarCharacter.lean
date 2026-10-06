import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RepresentationTheory.Character
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.FDRep

/-! # Scalar characters and their one-dimensional representations -/

noncomputable section

namespace Schubert.FiniteGroupCharacters.ScalarCharacter

/-- Multiplication by a scalar character gives the standard one-dimensional representation. -/
def representation {G : Type*} [Monoid G] (character : G →* ℂ) :
    Representation ℂ G ℂ :=
  (Algebra.lsmul ℂ ℂ ℂ).toMonoidHom.comp character

/-- The scalar representation evaluates by multiplication by the supplied character. -/
theorem apply_eq {G : Type*} [Monoid G]
    (character : G →* ℂ) (element : G) (value : ℂ) :
    representation character element value = character element * value := rfl

/-- The scalar representation has the supplied scalar as its trace. -/
theorem character {G : Type*} [Monoid G]
    (character : G →* ℂ) (element : G) :
    (representation character).character element = character element := by
  have hmap : representation character element =
      character element • (LinearMap.id : Module.End ℂ ℂ) := by
    apply LinearMap.ext
    intro value
    rfl
  change LinearMap.trace ℂ ℂ (representation character element) = _
  rw [hmap, map_smul]
  simp

/-- Every scalar-character representation is irreducible on its one-dimensional carrier. -/
theorem irreducible {G : Type*} [Monoid G]
    (character : G →* ℂ) : (representation character).IsIrreducible :=
  TauCeti.Representation.isIrreducible_of_finrank_eq_one _ (by simp)

/-- Two scalar-character objects are isomorphic exactly when their characters agree. -/
theorem iso_iff_eq {G : Type*} [Monoid G] (first second : G →* ℂ) :
    Nonempty (FDRep.of (representation first) ≅ FDRep.of (representation second)) ↔
      first = second := by
  constructor
  · rintro ⟨isomorphism⟩
    apply MonoidHom.ext
    intro element
    have hequal := congrFun (FDRep.char_iso isomorphism) element
    rw [FDRep.character_of, FDRep.character_of, character, character] at hequal
    exact hequal
  · rintro rfl
    exact ⟨CategoryTheory.Iso.refl _⟩

end Schubert.FiniteGroupCharacters.ScalarCharacter
