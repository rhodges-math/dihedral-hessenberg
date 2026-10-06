import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Dimensions of intertwiner spaces under embeddings -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G U V W : Type*} [Field K] [Monoid G]
variable [AddCommGroup U] [Module K U] [Module.Finite K U]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]
variable [AddCommGroup W] [Module K W] [Module.Finite K W]

omit [Module.Finite K V] in
/-- An injective intertwiner cannot decrease any intertwiner-space dimension. -/
theorem hom_finrank_mono (test : Representation K G U) {source : Representation K G V}
    {target : Representation K G W} (embedding : source.IntertwiningMap target)
    (hinjective : Function.Injective embedding) :
    Module.finrank K (test.IntertwiningMap source) ≤
      Module.finrank K (test.IntertwiningMap target) := by
  let post := Representation.IntertwiningMap.llcomp test source target embedding
  apply LinearMap.finrank_le_finrank_of_injective (f := post)
  intro first second hequal
  ext value
  apply hinjective
  have hvalue := congrArg (fun map : test.IntertwiningMap target => map value) hequal
  exact hvalue


/-- Intertwiners into a product split into their two coordinate intertwiners. -/
def homProdEquiv (test : Representation K G U) (first : Representation K G V)
    (second : Representation K G W) :
    (test.IntertwiningMap (first.prod second)) ≃ₗ[K]
      (test.IntertwiningMap first) × (test.IntertwiningMap second) where
  toFun map := ((Representation.IntertwiningMap.fst K first second).comp map,
    (Representation.IntertwiningMap.snd K first second).comp map)
  invFun maps := Representation.IntertwiningMap.prod maps.1 maps.2
  left_inv map := by ext value <;> rfl
  right_inv maps := by apply Prod.ext <;> rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two coordinate intertwiner dimensions add in the product representation. -/
theorem hom_finrank_prod (test : Representation K G U) (first : Representation K G V)
    (second : Representation K G W) :
    Module.finrank K (test.IntertwiningMap (first.prod second)) =
      Module.finrank K (test.IntertwiningMap first) +
        Module.finrank K (test.IntertwiningMap second) := by
  rw [(homProdEquiv test first second).finrank_eq, Module.finrank_prod]

omit [Module.Finite K U] [Module.Finite K V] [Module.Finite K W] in
/-- Representation equivalence preserves every intertwiner-space dimension. -/
theorem hom_finrank_equiv (test : Representation K G U) {first : Representation K G V}
    {second : Representation K G W} (equivalence : Representation.Equiv first second) :
    Module.finrank K (test.IntertwiningMap first) =
      Module.finrank K (test.IntertwiningMap second) := by
  let linear : (test.IntertwiningMap first) ≃ₗ[K] (test.IntertwiningMap second) :=
    { toFun := fun map => equivalence.toIntertwiningMap.comp map
      invFun := fun map => equivalence.symm.toIntertwiningMap.comp map
      left_inv := fun map => by
        ext value
        exact equivalence.toLinearEquiv.symm_apply_apply (map value)
      right_inv := fun map => by
        ext value
        exact equivalence.toLinearEquiv.apply_symm_apply (map value)
      map_add' := fun firstMap secondMap => by
        ext value
        change equivalence (firstMap value + secondMap value) =
          equivalence (firstMap value) + equivalence (secondMap value)
        exact equivalence.toLinearEquiv.map_add _ _
      map_smul' := fun scalar map => by
        ext value
        change equivalence (scalar • map value) = scalar • equivalence (map value)
        exact equivalence.toLinearEquiv.map_smul _ _ }
  exact linear.finrank_eq

end Schubert.FiniteGroupCharacters
