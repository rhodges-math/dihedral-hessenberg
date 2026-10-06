import Schubert.FiniteGroupCharacters.PermutationSpan
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Standard coset permutation actions on independent orbit spans -/

noncomputable section
namespace Schubert.FiniteGroupCharacters.PermutationSpan

variable {K G V : Type*} [Field K] [Group G] [MulAction G V]
variable [AddCommGroup V] [Module K V]

/-- Standard stabilizer cosets linearize to the span of an independent orbit. -/
theorem coset_equiv (source : Representation K G V)
    (haction : ∀ element value, element • value = source element value)
    (vector : V) (subgroup : Subgroup G)
    (hstabilizer : MulAction.stabilizer G vector = subgroup)
    (hindependent : LinearIndependent K
      (fun value : MulAction.orbit G vector => (value : V))) :
    Nonempty (Representation.Equiv (Representation.ofMulAction K G (G ⧸ subgroup))
      (action source (fun value : MulAction.orbit G vector => (value : V))
        (fun element value => (haction element value.val).symm))) := by
  subst subgroup
  let indices := (MulAction.orbitEquivQuotientStabilizer G vector).symm
  have hindices : ∀ (element : G) (value : G ⧸ MulAction.stabilizer G vector),
      indices (element • value) = element • indices value := by
    intro element value
    apply Subtype.ext
    exact MulAction.ofQuotientStabilizer_smul G vector element value
  exact ⟨(Schubert.FiniteGroupCharacters.permutationEquiv indices hindices).trans
    (equiv source (fun value : MulAction.orbit G vector => (value : V))
      (fun element value => (haction element value.val).symm) hindependent)⟩

end Schubert.FiniteGroupCharacters.PermutationSpan
