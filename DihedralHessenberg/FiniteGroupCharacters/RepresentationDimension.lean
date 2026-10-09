import DihedralHessenberg.FiniteGroupCharacters.GradedClass

/-! # Dimensions of representation classes -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- Evaluation of a virtual character at the identity gives its dimension. -/
def dimensionHom (field group : Type*) [Field field] [Monoid group] :
    TauCeti.repRing field group →+* field :=
  (Pi.evalRingHom (fun _ : group => field) 1).comp (TauCeti.repRingCharacter field group)

/-- The dimension of an object is its vector-space dimension. -/
theorem dimensionHom_of {field group : Type*} [Field field] [Monoid group]
    (representation : FDRep field group) :
    dimensionHom field group (TauCeti.SplitK0.of representation) =
      (Module.finrank field representation : field) := by
  simp only [dimensionHom, RingHom.comp_apply, TauCeti.repRingCharacter_of,
    Pi.evalRingHom_apply, FDRep.char_one]

/-- Taking dimensions of a graded class retains every degree dimension. -/
theorem graded_dimension_coeff {field group : Type*} [Field field] [Monoid group]
    (representation : GradedRepresentation field group) (degree : ℕ) :
    PowerSeries.coeff degree
      (PowerSeries.map (dimensionHom field group) (gradedClass representation)) =
        (Module.finrank field (representation degree) : field) := by
  rw [PowerSeries.coeff_map, gradedClass_coeff, dimensionHom_of]

end Schubert.FiniteGroupCharacters
