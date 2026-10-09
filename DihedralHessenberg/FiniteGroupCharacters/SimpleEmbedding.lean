import DihedralHessenberg.FiniteGroupCharacters.HomIntertwiner
import Mathlib.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Simple.Basic

/-! # Simple constituent embeddings from positive morphism dimensions -/

noncomputable section
open CategoryTheory
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Monoid G]

/-- A positive morphism dimension from a simple object gives an injective intertwiner. -/
theorem simple_embedding_of_hom_pos (source target : FDRep K G) [Simple source]
    (hpositive : 0 < Module.finrank K (source ⟶ target)) :
    ∃ embedding : Representation.IntertwiningMap source.ρ target.ρ,
      Function.Injective embedding := by
  obtain ⟨map, hmap⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpositive
  let embedding := homIntertwinerEquiv source target map
  have hnonzero : embedding ≠ 0 := by
    intro hzero
    apply hmap
    apply (homIntertwinerEquiv source target).injective
    simpa only [map_zero] using hzero
  let : Representation.IsIrreducible source.ρ :=
    (FDRep.simple_iff_isIrreducible source).mp inferInstance
  exact ⟨embedding,
    (Representation.IsIrreducible.injective_or_eq_zero embedding).resolve_right hnonzero⟩

end Schubert.FiniteGroupCharacters
