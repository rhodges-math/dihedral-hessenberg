import DihedralHessenberg.FiniteGroupCharacters.CharacterExpansion

/-! # Exact virtual multiplicities on the standard representation ring -/

noncomputable section
open CategoryTheory
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Group G] [Fintype G]

/-- The representation-ring character with its conjugation-invariant codomain. -/
def classCharacter : TauCeti.repRing K G →+ TauCeti.ClassFunction K G where
  toFun value := ⟨TauCeti.repRingCharacter K G value,
    TauCeti.repRingCharacter_mem_classFunction value⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' first second := Subtype.ext (map_add _ first second)

/-- Character pairing extends morphism multiplicities additively to virtual classes. -/
def classMultiplicity (test : FDRep K G) : TauCeti.repRing K G →+ K :=
  (TauCeti.ClassFunction.characterPairing (TauCeti.ClassFunction.ofFDRep test)).toAddMonoidHom.comp
    classCharacter

omit [Fintype G] in
/-- Bundling the character of an object preserves its exact class function. -/
theorem classCharacter_of (source : FDRep K G) :
    classCharacter (TauCeti.SplitK0.of source) = TauCeti.ClassFunction.ofFDRep source := by
  apply Subtype.ext
  exact TauCeti.repRingCharacter_of source

/-- Virtual multiplicity specializes to the standard morphism dimension. -/
theorem classMultiplicity_of [CharZero K] (test source : FDRep K G) :
    classMultiplicity test (TauCeti.SplitK0.of source) =
      (Module.finrank K (test ⟶ source) : K) := by
  let : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  change TauCeti.ClassFunction.characterPairing (TauCeti.ClassFunction.ofFDRep test)
    (classCharacter (TauCeti.SplitK0.of source)) = _
  rw [classCharacter_of, TauCeti.ClassFunction.characterPairing_symm,
    TauCeti.ClassFunction.characterPairing_ofFDRep_eq_finrank]

/-- A complete simple family determines every virtual representation class. -/
theorem class_eq_of_multiplicities [CharZero K] [IsAlgClosed K]
    {I : Type*} [Fintype I] (family : I → FDRep K G)
    (hsimple : ∀ index, Simple (family index))
    (hdistinct : ∀ first second, Nonempty (family first ≅ family second) → first = second)
    (hcard : Nat.card I = Nat.card (ConjClasses G))
    (first second : TauCeti.repRing K G)
    (hequal : ∀ index, classMultiplicity (family index) first =
      classMultiplicity (family index) second) : first = second := by
  let : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : ∀ index, Representation.IsIrreducible (family index).ρ := fun index =>
    (FDRep.simple_iff_isIrreducible (family index)).mp (hsimple index)
  have hind : Pairwise fun left right => IsEmpty
      (Representation.Equiv (family left).ρ (family right).ρ) := by
    intro left right hne
    exact ⟨fun equivalence => hne (hdistinct left right
      (TauCeti.nonempty_fdRepIso_iff.mpr ⟨equivalence⟩))⟩
  have hfunctions : classCharacter first = classCharacter second := by
    apply TauCeti.ClassFunction.eq_of_forall_characterPairing_ofCharacter_eq
      (fun index => (family index).ρ) hind hcard
    intro index
    rw [← TauCeti.ClassFunction.ofFDRep_eq_ofCharacter]
    exact hequal index
  apply TauCeti.repRingCharacter_injective
  exact congrArg Subtype.val hfunctions

end Schubert.FiniteGroupCharacters
