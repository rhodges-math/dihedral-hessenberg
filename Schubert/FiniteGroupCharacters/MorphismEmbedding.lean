import Schubert.FiniteGroupCharacters.MorphismDimension
import Schubert.FiniteGroupCharacters.HomDimension
import Schubert.FiniteGroupCharacters.HomIntertwiner

/-! # Morphism dimension bounds under embeddings -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Monoid G]

/-- An injective intertwiner preserves all morphism multiplicity lower bounds. -/
theorem hom_embedding_bound (test source target : FDRep K G)
    (embedding : Representation.IntertwiningMap source.ρ target.ρ)
    (hinjective : Function.Injective embedding) :
    Module.finrank K (test ⟶ source) ≤ Module.finrank K (test ⟶ target) := by
  rw [hom_intertwiner_finrank, hom_intertwiner_finrank]
  exact hom_finrank_mono test.ρ embedding hinjective
end Schubert.FiniteGroupCharacters
