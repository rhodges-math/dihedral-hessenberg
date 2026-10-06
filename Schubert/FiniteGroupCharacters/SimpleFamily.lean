import TauCeti.RepresentationTheory.CharacterTable.SimpleModuleCount

/-! # Completeness of finite families of pairwise distinct simple representations -/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace Schubert.FiniteGroupCharacters.SimpleFamily

/-- A simple family indexed by all conjugacy classes contains every simple object. -/
theorem complete {K G I : Type*} [Field K] [Group G] [Finite G]
    [IsSemisimpleRing K[G]] (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card (ConjClasses G) ≤ Nat.card I)
    (object : FDRep K G) [Simple object] :
    ∃ index, Nonempty (family index ≅ object) := by
  let classes : I → TauCeti.SimpleFDRepClasses K G := fun index =>
    @TauCeti.SimpleFDRepClasses.mk K G _ _ (family index) (hsimple index)
  have hinjective : Function.Injective classes := by
    intro first second hequal
    apply hdistinct first second
    let : Simple (family first) := hsimple first
    let : Simple (family second) := hsimple second
    exact (TauCeti.SimpleFDRepClasses.mk_eq_mk_iff _ _).mp hequal
  have hsurjective :=
    (TauCeti.SimpleFDRepClasses.bijective_of_injective_of_card_conjClasses_le
      hinjective hcard).2
  obtain ⟨index, hequal⟩ := hsurjective (TauCeti.SimpleFDRepClasses.mk object)
  refine ⟨index, ?_⟩
  let : Simple (family index) := hsimple index
  exact (TauCeti.SimpleFDRepClasses.mk_eq_mk_iff _ _).mp hequal

end Schubert.FiniteGroupCharacters.SimpleFamily
