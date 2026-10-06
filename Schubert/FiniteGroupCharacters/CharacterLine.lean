import Schubert.FiniteGroupCharacters.CharacterBasis

/-! # Characters of actions on a spanning line -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

/-- On a nonzero spanning eigenline, the character is the eigenvalue. -/
theorem character_line {K G V : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V]
    (action : Representation K G V) (vector : V) (hnonzero : vector ≠ 0)
    (hspan : Submodule.span K {vector} = ⊤) (element : G) (eigenvalue : K)
    (heigen : action element vector = eigenvalue • vector) :
    action.character element = eigenvalue := by
  let vectors : Fin 1 → V := fun _ => vector
  have hindependent : LinearIndependent K vectors := by
    apply linearIndependent_unique_iff.mpr
    exact hnonzero
  have hspanning : ⊤ ≤ Submodule.span K (Set.range vectors) := by
    simpa [vectors] using hspan.ge
  let basis := Module.Basis.mk hindependent hspanning
  have htrace := Eigenbasis.character_eq_sum action basis element (fun _ => eigenvalue) (by
    intro index
    simpa only [basis, Module.Basis.mk_apply] using heigen)
  simpa using htrace

end Schubert.FiniteGroupCharacters
