import DihedralHessenberg.FiniteGroupCharacters.GradedClass

/-! # Finite support of graded representation classes -/

noncomputable section

open scoped BigOperators

namespace Schubert.FiniteGroupCharacters

/-- Vanishing degree classes express the graded series as a finite monomial sum. -/
theorem gradedClass_eq_sum {K G : Type*} [Field K] [Monoid G]
    (family : GradedRepresentation K G) (bound : ℕ)
    (hvanish : ∀ degree, bound < degree →
      (TauCeti.SplitK0.of (family degree) : TauCeti.repRing K G) = 0) :
    gradedClass family = ∑ degree ∈ Finset.range (bound + 1),
      PowerSeries.monomial degree (TauCeti.SplitK0.of (family degree)) := by
  ext degree
  rw [gradedClass_coeff, map_sum]
  simp only [PowerSeries.coeff_monomial]
  by_cases hbelow : degree < bound + 1
  · simp [hbelow]
  · rw [hvanish degree (by omega)]
    simp [hbelow]

end Schubert.FiniteGroupCharacters
