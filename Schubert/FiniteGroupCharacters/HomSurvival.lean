import Schubert.FiniteGroupCharacters.EquivariantSplit
import Schubert.FiniteGroupCharacters.HomDimension

/-! # Intertwiner dimensions through finite-group quotients -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G U V W : Type*} [Field K] [Group G] [Finite G]
variable [NeZero (Nat.card G : K)]
variable [AddCommGroup U] [Module K U] [Module.Finite K U]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]
variable [AddCommGroup W] [Module K W] [Module.Finite K W]

/-- Intertwiners into a quotient split between its kernel and its target. -/
theorem hom_finrank_split (test : Representation K G U) {source : Representation K G V}
    {target : Representation K G W} (projection : source.IntertwiningMap target)
    (hsurjective : Function.Surjective projection) :
    Module.finrank K (test.IntertwiningMap source) =
      Module.finrank K (test.IntertwiningMap projection.ker.toRepresentation) +
        Module.finrank K (test.IntertwiningMap target) := by
  let : AddCommGroup projection.ker.toSubmodule := Submodule.addCommGroup _
  let : Module K projection.ker.toSubmodule := Submodule.module _
  obtain ⟨equivalence⟩ := equivariant_split projection hsurjective
  rw [← hom_finrank_equiv test equivalence, hom_finrank_prod]

/-- Constituents of an injected representation survive unless accounted for in the kernel. -/
theorem hom_survival_bound {A : Type*} [AddCommGroup A] [Module K A]
    (test : Representation K G U) (injected : Representation K G A)
    {source : Representation K G V} {target : Representation K G W}
    (embedding : injected.IntertwiningMap source) (hinjective : Function.Injective embedding)
    (projection : source.IntertwiningMap target) (hsurjective : Function.Surjective projection) :
    Module.finrank K (test.IntertwiningMap injected) ≤
      Module.finrank K (test.IntertwiningMap projection.ker.toRepresentation) +
        Module.finrank K (test.IntertwiningMap target) := by
  rw [← hom_finrank_split test projection hsurjective]
  exact hom_finrank_mono test embedding hinjective

end Schubert.FiniteGroupCharacters
