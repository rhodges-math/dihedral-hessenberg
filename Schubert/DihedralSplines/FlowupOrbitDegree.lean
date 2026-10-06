import Schubert.DihedralSplines.FlowupOrbitRepresentation

/-! # Orbit spans inside their homogeneous spline representation -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The span of homogeneous flow-up translates remains in that exact spline degree. -/
theorem orbit_degree (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.dotMulAction hthree
    Submodule.span ℂ (Set.range (fun value :
      MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
        (value : ideal.toRootSubset.Spline))) ≤
      ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) := by
  let := ideal.toRootSubset.dotMulAction hthree
  apply Submodule.span_le.mpr
  rintro value ⟨value, rfl⟩
  obtain ⟨element, hvalue⟩ := MulAction.mem_orbit_iff.mp value.property
  change value.val ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex)
  rw [← hvalue]
  exact ideal.toRootSubset.dot_mem_piece hthree element _ _ (homogeneous ideal vertex)

/-- Inclusion intertwines the orbit-span and homogeneous-piece actions. -/
def orbitPieceMap (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.dotMulAction hthree
    Representation.IntertwiningMap
      (PermutationSpan.action (ideal.toRootSubset.splineRepresentation hthree)
        (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
          (value : ideal.toRootSubset.Spline))
        (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree
          element value.val).symm))
      (ideal.toRootSubset.splinePieceRepresentation hthree (ideal.toRootSubset.length vertex)) := by
  let := ideal.toRootSubset.dotMulAction hthree
  exact
    { toLinearMap :=
        { toFun := fun value => ⟨value.val, orbit_degree ideal vertex value.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => by
        apply LinearMap.ext
        intro value
        rfl }

/-- The orbit span includes injectively in the spline degree. -/
theorem orbitPieceMap_injective (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.dotMulAction hthree
    Function.Injective (orbitPieceMap ideal vertex) := by
  let := ideal.toRootSubset.dotMulAction hthree
  intro first second hequal
  apply Subtype.ext
  have hvalue := congrArg (fun value :
    ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) => value.val) hequal
  exact hvalue

end Schubert.DihedralSplines.FlowupSpline
