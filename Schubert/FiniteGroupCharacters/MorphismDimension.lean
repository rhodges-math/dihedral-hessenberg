import Schubert.FiniteGroupCharacters.HomMultiplicity
import Schubert.FiniteGroupCharacters.FiniteSum

/-! # Morphism dimensions of finite-dimensional representations -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace Schubert.FiniteGroupCharacters
variable {K G : Type*} [Field K] [Monoid G]

/-- Morphism dimensions add over the standard binary biproduct. -/
theorem hom_biprod_finrank (test first second : FDRep K G) :
    Module.finrank K (test ⟶ first ⊞ second) =
      Module.finrank K (test ⟶ first) + Module.finrank K (test ⟶ second) := by
  let linear : (test ⟶ first ⊞ second) ≃ₗ[K] (test ⟶ first) × (test ⟶ second) :=
    { toFun := fun map => (map ≫ biprod.fst, map ≫ biprod.snd)
      invFun := fun maps => biprod.lift maps.1 maps.2
      left_inv := fun map => by apply biprod.hom_ext <;> simp
      right_inv := fun maps => by simp
      map_add' := fun firstMap secondMap => by simp [Preadditive.add_comp]
      map_smul' := fun scalar map => by simp [Linear.smul_comp] }
  rw [linear.finrank_eq, Module.finrank_prod]

/-- Target isomorphisms preserve the standard morphism dimension. -/
theorem hom_iso_finrank (test : FDRep K G) {first second : FDRep K G}
    (equivalence : first ≅ second) :
    Module.finrank K (test ⟶ first) = Module.finrank K (test ⟶ second) := by
  let linear : (test ⟶ first) ≃ₗ[K] (test ⟶ second) :=
    { toFun := fun map => map ≫ equivalence.hom
      invFun := fun map => map ≫ equivalence.inv
      left_inv := fun map => by simp
      right_inv := fun map => by simp
      map_add' := fun _ _ => by simp [Preadditive.add_comp]
      map_smul' := fun _ _ => by simp [Linear.smul_comp] }
  exact linear.finrank_eq

end Schubert.FiniteGroupCharacters
