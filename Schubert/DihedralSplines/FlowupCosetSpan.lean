import Schubert.DihedralSplines.SplineOrbitAction
import Schubert.FiniteGroupCharacters.OrbitSpan
import Schubert.DihedralSplines.FlowupOrbitStabilizer
import Schubert.Dihedral.CosetFDRep

/-! # High flow-up orbits and their standard root-reflection cosets -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The high flow-up stabilizer is exactly the simple-root reflection subgroup. -/
theorem high_subgroup (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    letI := ideal.toRootSubset.dotMulAction hthree
    MulAction.stabilizer (DihedralGroup n) (spline ideal vertex) = alpha.subgroup := by
  let := ideal.toRootSubset.dotMulAction hthree
  ext element
  change ideal.toRootSubset.dot hthree element (spline ideal vertex) = spline ideal vertex ↔
    element ∈ alpha.subgroup
  rw [high_stabilizer ideal vertex alpha hsimple hascent hhalf hedge]
  change (element = 1 ∨ element = rootReflection alpha.index) ↔
    element ∈ Subgroup.closure {rootReflection alpha.index}
  rw [rootReflection_eq_sr, mem_closure_sr_iff]

/-- The standard root coset action is the independent high flow-up orbit span. -/
theorem high_coset_span (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    letI := ideal.toRootSubset.dotMulAction hthree
    LinearIndependent ℂ (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
      (value : ideal.toRootSubset.Spline)) →
    Nonempty (Representation.Equiv alpha.cosetRepresentation
      (PermutationSpan.action (ideal.toRootSubset.splineRepresentation hthree)
        (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
          (value : ideal.toRootSubset.Spline))
        (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree
          element value.val).symm))) := by
  let := ideal.toRootSubset.dotMulAction hthree
  intro hindependent
  exact PermutationSpan.coset_equiv (ideal.toRootSubset.splineRepresentation hthree)
    (ideal.toRootSubset.dotMulAction_apply hthree) (spline ideal vertex) alpha.subgroup
    (high_subgroup ideal vertex alpha hsimple hascent hhalf hedge) hindependent

end Schubert.DihedralSplines.FlowupSpline
