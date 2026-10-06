import Schubert.DihedralSplines.FlowupOrbitLinear

/-! # Standard root-coset objects on high flow-up spline orbit spans -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The finite representation on the span of the dot orbit. -/
def orbitFDRep (vertex : DihedralGroup n)
    (hindependent : letI := ideal.toRootSubset.dotMulAction hthree
      LinearIndependent ℂ (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
        (value : ideal.toRootSubset.Spline))) : FDRep ℂ (DihedralGroup n) := by
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal vertex)).fintype
  exact PermutationSpan.fdRep (ideal.toRootSubset.splineRepresentation hthree)
    (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
      (value : ideal.toRootSubset.Spline))
    (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    hindependent

/-- The independent high flow-up span is the simple-root coset object. -/
theorem high_coset_iso (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hindependent : letI := ideal.toRootSubset.dotMulAction hthree
      LinearIndependent ℂ (fun value : MulAction.orbit (DihedralGroup n) (spline ideal vertex) =>
        (value : ideal.toRootSubset.Spline))) :
    Nonempty (alpha.cosetFDRep ≅ orbitFDRep ideal vertex hindependent) := by
  let := ideal.toRootSubset.dotMulAction hthree
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact high_coset_span ideal vertex alpha hsimple hascent hhalf hedge hindependent

/-- The high orbit under short selection is the standard simple-root coset object.
  -/
theorem high_short_iso
    (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hbound : 2 * (n - length n hthree vertex - 1) + 1 < n)
    (hselected : ∀ beta : PositiveRoot n,
      length n hthree beta.reflection ≤ 2 * (n - length n hthree vertex - 1) + 1 →
        beta.val ∈ ideal) :
    Nonempty (alpha.cosetFDRep ≅ orbitFDRep ideal vertex
      (orbit_independent_short ideal vertex alpha hsimple hascent hhalf hedge hbound hselected)) :=
  high_coset_iso ideal vertex alpha hsimple hascent hhalf hedge
    (orbit_independent_short ideal vertex alpha hsimple hascent hhalf hedge hbound hselected)

/-- The high orbit under odd selection is the standard simple-root coset object. -/
theorem high_odd_iso
    (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges)
    (hcard : ideal.carrier.ncard = 2 * (n - length n hthree vertex - 1) + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) :
    Nonempty (alpha.cosetFDRep ≅ orbitFDRep ideal vertex
      (orbit_independent_odd ideal vertex alpha hsimple hascent hhalf hedge hcard hproper)) :=
  high_coset_iso ideal vertex alpha hsimple hascent hhalf hedge
    (orbit_independent_odd ideal vertex alpha hsimple hascent hhalf hedge hcard hproper)

end Schubert.DihedralSplines.FlowupSpline
