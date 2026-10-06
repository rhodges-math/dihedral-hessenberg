import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import Mathlib.RepresentationTheory.Intertwining

/-! # Equivariant sections of finite-group quotient maps -/

noncomputable section

open scoped MonoidAlgebra

namespace Schubert.FiniteGroupCharacters

/-- A surjective intertwiner for a finite group of invertible order has an equivariant section. -/
theorem equivariant_section {K G V W : Type*} [Field K] [Group G] [Finite G]
    [NeZero (Nat.card G : K)] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    {source : Representation K G V} {target : Representation K G W}
    (projection : source.IntertwiningMap target) (hsurjective : Function.Surjective projection) :
    ∃ lift : target.IntertwiningMap source,
      ∀ value, projection (lift value) = value := by
  let groupMap := Representation.IntertwiningMap.equivLinearMapAsModule source target projection
  let : Module.Projective K[G] target.asModule := Module.projective_of_isSemisimpleRing _ _
  have hsurj : Function.Surjective groupMap := hsurjective
  obtain ⟨lift, hlift⟩ := groupMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule target source).symm lift, ?_⟩
  intro value
  exact DFunLike.congr_fun hlift value

end Schubert.FiniteGroupCharacters
