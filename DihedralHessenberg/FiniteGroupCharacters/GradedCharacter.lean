import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Degreewise characters of finite-dimensional representations

A graded representation is a family of the standard finite-dimensional bundled
representations. Its character records the trace in each degree independently.
-/

noncomputable section

open CategoryTheory

namespace Schubert.FiniteGroupCharacters

universe u v

/-- Degreewise finite-dimensional representations, with grading indexed by natural numbers. -/
abbrev GradedRepresentation (field : Type u) (group : Type v) [Field field] [Monoid group] :=
  ℕ → FDRep field group

/-- Degreewise character values on a group. -/
abbrev GradedCharacter (field : Type u) (group : Type v) := ℕ → group → field

/-- The degreewise trace character of a graded finite-dimensional representation. -/
def gradedCharacter {field : Type u} {group : Type v} [Field field] [Monoid group]
    (representation : GradedRepresentation field group) : GradedCharacter field group :=
  fun degree => (representation degree).character

/-- The identity character value is the dimension of the corresponding graded piece. -/
theorem gradedCharacter_one {field : Type u} {group : Type v} [Field field] [Monoid group]
    (representation : GradedRepresentation field group) (degree : ℕ) :
    gradedCharacter representation degree 1 = Module.finrank field (representation degree) :=
  FDRep.char_one _

/-- Isomorphic representations in each degree have the same graded character. -/
theorem gradedCharacter_eq_of_degreewise_iso {field : Type u} {group : Type v}
    [Field field] [Monoid group] (first second : GradedRepresentation field group)
    (hisomorphic : ∀ degree, Nonempty (first degree ≅ second degree)) :
    gradedCharacter first = gradedCharacter second := by
  funext degree
  obtain ⟨isomorphism⟩ := hisomorphic degree
  exact FDRep.char_iso isomorphism

/-- Graded characters are invariant under conjugation. -/
theorem gradedCharacter_conjugate {field : Type u} {group : Type v} [Field field] [Group group]
    (representation : GradedRepresentation field group) (degree : ℕ) (element byElement : group) :
    gradedCharacter representation degree (byElement * element * byElement⁻¹) =
      gradedCharacter representation degree element := by
  change Representation.character (representation degree).ρ (byElement * element * byElement⁻¹) = _
  rw [Representation.char_mul_comm]
  simp only [inv_mul_cancel_left]
  exact FDRep.character_ρ _ _

/-- For finite groups in characteristic zero, graded characters determine each graded piece. -/
theorem degreewise_iso_iff_gradedCharacter_eq {field : Type u} {group : Type v}
    [Field field] [CharZero field] [Group group] [Finite group]
    (first second : GradedRepresentation field group) :
    (∀ degree, Nonempty (first degree ≅ second degree)) ↔
      gradedCharacter first = gradedCharacter second := by
  constructor
  · exact gradedCharacter_eq_of_degreewise_iso first second
  · intro hequal degree
    exact FDRep.nonempty_iso_of_character_eq _ _ (congrFun hequal degree)

end Schubert.FiniteGroupCharacters
