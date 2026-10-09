import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariant identification with the range -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G V W : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {source : Representation K G V} {target : Representation K G W}

/-- An intertwiner maps to its invariant range without changing its values. -/
def rangeIntertwiner (embedding : Representation.IntertwiningMap source target) :
    Representation.IntertwiningMap source embedding.range.toRepresentation where
  toLinearMap := embedding.toLinearMap.rangeRestrict
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining source target embedding element value

/-- An injective intertwiner identifies its source with the inherited range action. -/
def rangeActionEquiv (embedding : Representation.IntertwiningMap source target)
    (hinjective : Function.Injective embedding) :
    Representation.Equiv source embedding.range.toRepresentation :=
  Representation.IntertwiningMap.ofBijective (rangeIntertwiner embedding)
    ⟨fun first second hequal => hinjective (congrArg Subtype.val hequal),
      fun value => by
        obtain ⟨original, horiginal⟩ := value.property
        exact ⟨original, Subtype.ext horiginal⟩⟩

/-- The range identification is the intertwiner on underlying vectors. -/
theorem rangeActionEquiv_apply (embedding : Representation.IntertwiningMap source target)
    (hinjective : Function.Injective embedding) (value : V) :
    (rangeActionEquiv embedding hinjective value : W) = embedding value := rfl

end Schubert.FiniteGroupCharacters
