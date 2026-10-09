import DihedralHessenberg.FiniteGroupCharacters.GradedCharacter
import TauCeti.RepresentationTheory.RepresentationRing.Injective
import Mathlib.RingTheory.PowerSeries.Basic

/-! # Graded classes in the finite-dimensional representation ring -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

universe u v

/-- The formal degree series with coefficients in the standard representation ring. -/
def gradedClass {field : Type u} {group : Type v} [Field field] [Monoid group]
    (representation : GradedRepresentation field group) :
    PowerSeries (TauCeti.repRing field group) :=
  PowerSeries.mk fun degree => TauCeti.SplitK0.of (representation degree)

/-- Each coefficient is the class of the corresponding degree representation. -/
theorem gradedClass_coeff {field : Type u} {group : Type v} [Field field] [Monoid group]
    (representation : GradedRepresentation field group) (degree : ℕ) :
    PowerSeries.coeff degree (gradedClass representation) =
      TauCeti.SplitK0.of (representation degree) := by
  simp [gradedClass]

/-- In characteristic zero, equality of graded classes is exactly equality of graded traces. -/
theorem gradedClass_eq_iff {field : Type u} {group : Type v}
    [Field field] [CharZero field] [Group group] [Finite group]
    (first second : GradedRepresentation field group) :
    gradedClass first = gradedClass second ↔ gradedCharacter first = gradedCharacter second := by
  constructor
  · intro hequal
    funext degree
    have hcoefficient := congrArg (PowerSeries.coeff degree) hequal
    rw [gradedClass_coeff, gradedClass_coeff] at hcoefficient
    have htrace := congrArg (TauCeti.repRingCharacter field group) hcoefficient
    simpa only [TauCeti.repRingCharacter_of, gradedCharacter] using htrace
  · intro hequal
    apply PowerSeries.ext
    intro degree
    rw [gradedClass_coeff, gradedClass_coeff]
    apply TauCeti.repRingCharacter_injective
    simpa only [TauCeti.repRingCharacter_of, gradedCharacter] using congrFun hequal degree

/-- Equality of graded classes determines isomorphisms in every degree. -/
theorem gradedClass_eq_iff_iso {field : Type u} {group : Type v}
    [Field field] [CharZero field] [Group group] [Finite group]
    (first second : GradedRepresentation field group) :
    gradedClass first = gradedClass second ↔
      ∀ degree, Nonempty (first degree ≅ second degree) := by
  rw [gradedClass_eq_iff, ← degreewise_iso_iff_gradedCharacter_eq]

end Schubert.FiniteGroupCharacters
