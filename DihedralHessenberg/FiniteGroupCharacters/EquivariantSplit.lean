import DihedralHessenberg.FiniteGroupCharacters.EquivariantSection
import DihedralHessenberg.FiniteGroupCharacters.PermutationSum
import TauCeti.RepresentationTheory.RepresentationRing.Basic

/-! # Equivariant splitting into a kernel and quotient -/

noncomputable section
namespace Schubert.FiniteGroupCharacters
variable {K G V W : Type*} [Field K] [Group G] [Finite G]
variable [NeZero (Nat.card G : K)] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

/-- A finite-group quotient is the direct product of its kernel and target. -/
theorem equivariant_split {source : Representation K G V} {target : Representation K G W}
    (projection : source.IntertwiningMap target) (hsurjective : Function.Surjective projection) :
    Nonempty (Representation.Equiv (projection.ker.toRepresentation.prod target) source) := by
  obtain ⟨lift, hsection⟩ := equivariant_section projection hsurjective
  let splitting : (projection.ker.toSubmodule × W) ≃ₗ[K] V :=
    { toFun := fun value => value.1.val + lift value.2
      invFun := fun value =>
        (⟨value - lift (projection value), by
          change projection (value - lift (projection value)) = 0
          rw [map_sub, hsection, sub_self]⟩, projection value)
      left_inv := by
        intro value
        apply Prod.ext
        · apply Subtype.ext
          change value.1.val + lift value.2 - lift (projection (value.1.val + lift value.2)) =
            value.1.val
          rw [map_add, hsection]
          have hzero : projection value.1.val = 0 := value.1.property
          rw [hzero, zero_add, add_sub_cancel_right]
        · change projection (value.1.val + lift value.2) = value.2
          rw [map_add, hsection]
          have hzero : projection value.1.val = 0 := value.1.property
          rw [hzero, zero_add]
      right_inv := by
        intro value
        change value - lift (projection value) + lift (projection value) = value
        exact sub_add_cancel _ _
      map_add' := by
        intro first second
        change first.1.val + second.1.val + lift (first.2 + second.2) =
          (first.1.val + lift first.2) + (second.1.val + lift second.2)
        rw [map_add]
        abel
      map_smul' := by
        intro scalar value
        change scalar • value.1.val + lift (scalar • value.2) =
          scalar • (value.1.val + lift value.2)
        rw [map_smul, smul_add] }
  refine ⟨Representation.Equiv.mk splitting ?_⟩
  intro element
  apply LinearMap.ext
  intro value
  change source element value.1.val + lift (target element value.2) =
    source element (value.1.val + lift value.2)
  rw [map_add, lift.isIntertwining target source element value.2]

end Schubert.FiniteGroupCharacters

namespace Schubert.FiniteGroupCharacters
open CategoryTheory Limits
variable {G V W : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
variable [Module.Finite ℂ V] [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

/-- A finite quotient class is its source class minus its kernel class. -/
theorem quotient_class {source : Representation ℂ G V} {target : Representation ℂ G W}
    (projection : source.IntertwiningMap target) (hsurjective : Function.Surjective projection) :
    (TauCeti.SplitK0.of (FDRep.of target) : TauCeti.repRing ℂ G) =
      TauCeti.SplitK0.of (FDRep.of source) -
        TauCeti.SplitK0.of (FDRep.of projection.ker.toRepresentation) := by
  let : NeZero (Nat.card G : ℂ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let : AddCommGroup projection.ker.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ projection.ker.toSubmodule := Submodule.module _
  obtain ⟨equivalence⟩ := equivariant_split projection hsurjective
  have hsource : Nonempty (FDRep.of (projection.ker.toRepresentation.prod target) ≅
      FDRep.of source) := TauCeti.nonempty_fdRepIso_iff.mpr ⟨equivalence⟩
  obtain ⟨sourceIso⟩ := hsource
  obtain ⟨productIso⟩ := product_iso projection.ker.toRepresentation target
  have hclass : (TauCeti.SplitK0.of (FDRep.of source) : TauCeti.repRing ℂ G) =
      TauCeti.SplitK0.of (FDRep.of projection.ker.toRepresentation) +
        TauCeti.SplitK0.of (FDRep.of target) := by
    exact (TauCeti.SplitK0.of_congr (sourceIso.symm ≪≫ productIso)).trans
      (TauCeti.SplitK0.of_biprod _ _)
  rw [hclass]
  abel

end Schubert.FiniteGroupCharacters
