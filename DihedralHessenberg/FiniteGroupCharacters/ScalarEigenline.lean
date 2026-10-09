import DihedralHessenberg.FiniteGroupCharacters.ScalarCharacter
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Scalar representations on one-dimensional eigenlines -/

noncomputable section
namespace Schubert.FiniteGroupCharacters.ScalarCharacter

/-- A nonzero eigenvector spanning a one-dimensional action gives a scalar equivalence. -/
def eigenlineEquiv {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (source : Representation ℂ G V) (character : G →* ℂ)
    (vector : V) (hnonzero : vector ≠ 0) (hdimension : Module.finrank ℂ V = 1)
    (hvector : ∀ element, source element vector = character element • vector) :
    Representation.Equiv (representation character) source := by
  let embed := LinearMap.toSpanSingleton ℂ V vector
  have hinjective : Function.Injective embed := smul_left_injective ℂ hnonzero
  have hsurjective : Function.Surjective embed :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdimension.symm)).mp hinjective
  refine Representation.Equiv.mk (LinearEquiv.ofBijective embed ⟨hinjective, hsurjective⟩) ?_
  intro element
  apply LinearMap.ext
  intro scalar
  change (character element * scalar) • vector = source element (scalar • vector)
  rw [map_smul, hvector, mul_smul, smul_comm]

end Schubert.FiniteGroupCharacters.ScalarCharacter
