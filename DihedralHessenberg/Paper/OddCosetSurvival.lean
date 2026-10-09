import DihedralHessenberg.Paper.QuotientSurvival
import DihedralHessenberg.Paper.FlowupOrbitDegree

/-! # Odd middle orbit constituents in coordinate quotients -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- The odd middle coset can lose only constituents in the kernel. -/
theorem odd_coset_survival (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1))
    (test : FDRep ℂ (DihedralGroup n)) :
    Module.finrank ℂ (test ⟶ alpha.cosetFDRep) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal half) +
        Module.finrank ℂ (test ⟶ RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  let := ideal.toRootSubset.dotMulAction hthree
  have hbounds := witness.odd_bounds hcard hproper
  let independent := FlowupSpline.orbit_independent_odd ideal witness.vertex alpha hsimple
    witness.ascent hbounds.2.1 witness.selected (witness.odd_card hcard hproper) hproper
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    (FlowupSpline.high_coset_iso ideal witness.vertex alpha hsimple witness.ascent
      hbounds.2.1 witness.selected independent)
  let embedding := (FlowupSpline.orbitPieceMap ideal witness.vertex).comp
    equivalence.toIntertwiningMap
  have hbound := quotient_survival ideal (ideal.toRootSubset.length witness.vertex) test
    alpha.cosetFDRep embedding ((FlowupSpline.orbitPieceMap_injective ideal witness.vertex).comp
      equivalence.toLinearEquiv.injective)
  have hdegree := witness.degree
  change ideal.length witness.vertex = half at hdegree
  rw [hdegree] at hbound
  exact hbound
end Left

namespace Right
/-- The odd middle coset can lose only constituents in the kernel. -/
theorem odd_coset_survival (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1))
    (test : FDRep ℂ (DihedralGroup n)) :
    Module.finrank ℂ (test ⟶ alpha.cosetFDRep) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal half) +
        Module.finrank ℂ (test ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
  let := ideal.toRootSubset.dotMulAction hthree
  have hbounds := witness.odd_bounds hcard hproper
  let independent := FlowupSpline.orbit_independent_odd ideal witness.vertex alpha hsimple
    witness.ascent hbounds.2.1 witness.selected (witness.odd_card hcard hproper) hproper
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    (FlowupSpline.high_coset_iso ideal witness.vertex alpha hsimple witness.ascent
      hbounds.2.1 witness.selected independent)
  let embedding := (FlowupSpline.orbitPieceMap ideal witness.vertex).comp
    equivalence.toIntertwiningMap
  have hbound := quotient_survival ideal (ideal.toRootSubset.length witness.vertex) test
    alpha.cosetFDRep embedding ((FlowupSpline.orbitPieceMap_injective ideal witness.vertex).comp
      equivalence.toLinearEquiv.injective)
  have hdegree := witness.degree
  change ideal.length witness.vertex = half at hdegree
  rw [hdegree] at hbound
  exact hbound
end Right

end Schubert.DihedralSplines.HessenbergIdeal
