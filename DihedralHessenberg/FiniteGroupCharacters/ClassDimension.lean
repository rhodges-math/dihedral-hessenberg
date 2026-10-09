import DihedralHessenberg.FiniteGroupCharacters.GradedClass

/-! # Zero-dimensional representation classes -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Group G] [Finite G] [CharZero K]

/-- A representation of dimension zero has zero class. -/
theorem class_zero_of_finrank (source : FDRep K G)
    (hzero : Module.finrank K source = 0) :
    (TauCeti.SplitK0.of source : TauCeti.repRing K G) = 0 := by
  have : Subsingleton source := (Module.finrank_eq_zero_iff_of_free K source).mp hzero
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_zero]
  funext element
  change LinearMap.trace K source (source.ρ element) = 0
  rw [Subsingleton.elim (source.ρ element) 0, map_zero]

end Schubert.FiniteGroupCharacters


/-! # The unit class of the trivial representation -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Group G] [Finite G] [CharZero K]

/-- The scalar trivial representation is the representation-ring unit. -/
theorem trivial_class_one :
    (TauCeti.SplitK0.of (FDRep.of (Representation.trivial K G K)) : TauCeti.repRing K G) = 1 := by
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_one]
  funext element
  exact FDRep.character_of_trivial element

end Schubert.FiniteGroupCharacters
