import TauCeti.RepresentationTheory.CharacterTable.Completeness
import TauCeti.RepresentationTheory.CharacterTable.Determined
import TauCeti.RepresentationTheory.Simple.Basic
import TauCeti.RepresentationTheory.RepresentationRing.Injective

/-! # Exact multiplicity expansions for complete finite simple families -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters.SimpleFamily
variable {K G I : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [Group G] [Finite G] [Fintype I]

/-- A complete simple character family expands every representation by Hom multiplicities. -/
theorem character_expansion (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G)) (source : FDRep K G) :
    source.character = ∑ index, Module.finrank K (family index ⟶ source) •
      (family index).character := by
  let : Fintype G := Fintype.ofFinite G
  let : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ∀ index, Representation.IsIrreducible (family index).ρ := fun index =>
    (FDRep.simple_iff_isIrreducible (family index)).mp (hsimple index)
  have hind : Pairwise fun first second => IsEmpty
      (Representation.Equiv (family first).ρ (family second).ρ) := by
    intro first second hne
    exact ⟨fun equivalence => hne (hdistinct first second
      (TauCeti.nonempty_fdRepIso_iff.mpr ⟨equivalence⟩))⟩
  have hexpansion := TauCeti.ClassFunction.sum_characterPairing_smul_ofCharacter
    (fun index => (family index).ρ) hind hcard (TauCeti.ClassFunction.ofFDRep source)
  have hcoeff (index : I) : TauCeti.ClassFunction.characterPairing
      (TauCeti.ClassFunction.ofCharacter (family index).ρ)
      (TauCeti.ClassFunction.ofFDRep source) =
        (Module.finrank K (family index ⟶ source) : K) := by
    rw [← TauCeti.ClassFunction.ofFDRep_eq_ofCharacter,
      TauCeti.ClassFunction.characterPairing_symm,
      TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank]
  simp_rw [hcoeff] at hexpansion
  have hfunctions := congrArg (TauCeti.ClassFunction K G).subtype hexpansion.symm
  funext element
  have hvalue := congrFun hfunctions element
  simpa only [map_sum, map_smul, map_nsmul, Nat.cast_smul_eq_nsmul,
    Finset.sum_apply, Pi.smul_apply, Submodule.subtype_apply,
    TauCeti.ClassFunction.ofFDRep_apply, TauCeti.ClassFunction.ofCharacter_apply,
    FDRep.character, Representation.character] using hvalue

/-- Complete simple multiplicities exhaust the dimension of the carrier. -/
theorem dimension_sum (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G)) (source : FDRep K G) :
    Module.finrank K source = ∑ index, Module.finrank K (family index ⟶ source) *
      Module.finrank K (family index) := by
  have hvalue := congrFun (character_expansion family hsimple hdistinct hcard source) 1
  simp only [Finset.sum_apply, Pi.smul_apply, FDRep.char_one] at hvalue
  simp only [nsmul_eq_mul] at hvalue
  exact_mod_cast hvalue

/-- The representation-ring class is an effective sum with Hom dimensions. -/
theorem class_expansion (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G)) (source : FDRep K G) :
    (TauCeti.SplitK0.of source : TauCeti.repRing K G) =
      ∑ index, Module.finrank K (family index ⟶ source) • TauCeti.SplitK0.of (family index) := by
  apply TauCeti.repRingCharacter_injective
  simp only [map_sum, map_nsmul, TauCeti.repRingCharacter_of]
  exact character_expansion family hsimple hdistinct hcard source

/-- Exact multiplicity equality gives an isomorphism of the objects. -/
theorem iso_of_multiplicities (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G)) (first second : FDRep K G)
    (hequal : ∀ index, Module.finrank K (family index ⟶ first) =
      Module.finrank K (family index ⟶ second)) : Nonempty (first ≅ second) := by
  apply FDRep.nonempty_iso_of_character_eq
  rw [character_expansion family hsimple hdistinct hcard first,
    character_expansion family hsimple hdistinct hcard second]
  simp only [hequal]

end Schubert.FiniteGroupCharacters.SimpleFamily
