import Mathlib.RepresentationTheory.FDRep

/-! # Linear identification of standard representation morphisms and intertwiners -/

noncomputable section
open CategoryTheory
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Monoid G]

/-- Standard finite representation morphisms are the linear intertwiners. -/
def homIntertwinerEquiv (first second : FDRep K G) :
    (first ⟶ second) ≃ₗ[K] Representation.IntertwiningMap first.ρ second.ρ :=
  (FDRep.forget₂HomLinearEquiv first second).symm.trans
    (Rep.homLinearEquiv ((forget₂ (FDRep K G) (Rep K G)).obj first)
      ((forget₂ (FDRep K G) (Rep K G)).obj second))

/-- Standard morphism and intertwiner dimensions agree exactly. -/
theorem hom_intertwiner_finrank (first second : FDRep K G) :
    Module.finrank K (first ⟶ second) =
      Module.finrank K (Representation.IntertwiningMap first.ρ second.ρ) :=
  (homIntertwinerEquiv first second).finrank_eq

end Schubert.FiniteGroupCharacters
