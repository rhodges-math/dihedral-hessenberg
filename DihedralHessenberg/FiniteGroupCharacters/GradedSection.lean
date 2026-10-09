import DihedralHessenberg.FiniteGroupCharacters.EquivariantSection
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Assembly of graded equivariant sections -/

noncomputable section

namespace Schubert.FiniteGroupCharacters

variable {K G V W : Type*} [Field K] [Monoid G]
variable [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
variable {source : Representation K G V} {target : Representation K G W}
variable (sourcePieces : ℕ → Subrepresentation source)
variable (targetPieces : ℕ → Subrepresentation target)
variable [DirectSum.Decomposition (fun degree => (targetPieces degree).toSubmodule)]
variable (lifts : ∀ degree,
  (targetPieces degree).toRepresentation.IntertwiningMap
    (sourcePieces degree).toRepresentation)

/-- Homogeneous equivariant lifts assemble to a linear map on the direct-sum grading. -/
def gradedLift : W →ₗ[K] V :=
  (DirectSum.toModule K ℕ V fun degree =>
    (sourcePieces degree).toSubmodule.subtype.comp (lifts degree).toLinearMap).comp
      (DirectSum.decomposeLinearEquiv (fun degree => (targetPieces degree).toSubmodule)).toLinearMap

/-- The assembled lift agrees with the selected lift on each homogeneous piece. -/
theorem gradedLift_piece (degree : ℕ) (value : (targetPieces degree).toSubmodule) :
    gradedLift sourcePieces targetPieces lifts value.val =
      (lifts degree value : V) := by
  simp only [gradedLift, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    DirectSum.decomposeLinearEquiv_apply_coe, DirectSum.toModule_lof]
  rfl

/-- Degreewise right inverse identities give the right inverse on the full graded representation. -/
theorem gradedLift_rightInverse (projection : source.IntertwiningMap target)
    (hprojection : ∀ degree (value : (targetPieces degree).toSubmodule),
      projection (lifts degree value : V) = value.val) :
    projection.toLinearMap.comp (gradedLift sourcePieces targetPieces lifts) = LinearMap.id := by
  apply DirectSum.decompose_lhom_ext (fun degree => (targetPieces degree).toSubmodule)
  intro degree
  apply LinearMap.ext
  intro value
  change projection (gradedLift sourcePieces targetPieces lifts value.val) = value.val
  rw [gradedLift_piece]
  exact hprojection degree value

/-- The assembled homogeneous lift intertwines the whole actions. -/
theorem gradedLift_equivariant (element : G) (value : W) :
    gradedLift sourcePieces targetPieces lifts (target element value) =
      source element (gradedLift sourcePieces targetPieces lifts value) := by
  have hmap : (gradedLift sourcePieces targetPieces lifts).comp (target element) =
      (source element).comp (gradedLift sourcePieces targetPieces lifts) := by
    apply DirectSum.decompose_lhom_ext (fun degree => (targetPieces degree).toSubmodule)
    intro degree
    apply LinearMap.ext
    intro homogeneous
    change gradedLift sourcePieces targetPieces lifts
      ((targetPieces degree).toRepresentation element homogeneous : W) =
        source element (gradedLift sourcePieces targetPieces lifts homogeneous.val)
    rw [gradedLift_piece, gradedLift_piece]
    exact congrArg Subtype.val ((lifts degree).isIntertwining _ _ element homogeneous)
  exact DFunLike.congr_fun hmap value

end Schubert.FiniteGroupCharacters
