import TauCeti.RepresentationTheory.RepresentationRing.Injective

/-! # Morphism multiplicities from effective representation classes -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters
variable {G I : Type*} [Group G] [Finite G] [Fintype I]

/-- A natural representation-class sum gives exact morphism multiplicities. -/
theorem hom_finrank_of_class (test source : FDRep ℂ G) (family : I → FDRep ℂ G)
    (multiplicity : I → ℕ)
    (hclass : (TauCeti.SplitK0.of source : TauCeti.repRing ℂ G) =
      ∑ index, multiplicity index • TauCeti.SplitK0.of (family index)) :
    Module.finrank ℂ (test ⟶ source) =
      ∑ index, multiplicity index * Module.finrank ℂ (test ⟶ family index) := by
  apply FDRep.finrank_hom_eq_sum_of_character_eq test
  have hcharacter := congrArg (TauCeti.repRingCharacter ℂ G) hclass
  simpa only [map_sum, map_nsmul, TauCeti.repRingCharacter_of] using hcharacter

end Schubert.FiniteGroupCharacters
