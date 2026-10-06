import Schubert.Dihedral.RootScalarCosetBound
import Schubert.DihedralSplines.ScalarKernel
import Schubert.DihedralSplines.OddCosetSurvival

/-! # The chosen even scalar in odd middle quotient actions -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- The odd middle retains the scalar character selected by its simple root. -/
theorem odd_scalar_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1)) (heven : Even n) :
    1 ≤ Module.finrank ℂ (alpha.scalarFDRep heven ⟶
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  let : Simple (alpha.scalarFDRep heven) := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_simple n heven _
  have hdimension : Module.finrank ℂ (alpha.scalarFDRep heven) = 1 := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_finrank n heven _
  have hnot : ¬ Nonempty (alpha.scalarFDRep heven ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
    unfold PositiveRoot.scalarFDRep
    exact even_scalar_not_trivial heven _
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hbound := odd_coset_survival ideal half hcard hproper alpha hsimple witness
    (alpha.scalarFDRep heven)
  rw [removed_scalar_zero ideal half (by omega) hproper (by omega) _ hdimension hnot,
    zero_add] at hbound
  exact (root_scalar_coset_bound alpha heven).trans hbound
end Left

namespace Right
/-- The odd middle retains the scalar character selected by its simple root. -/
theorem odd_scalar_bound (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (witness : MiddleWitness ideal half alpha (n - half - 1)) (heven : Even n) :
    1 ≤ Module.finrank ℂ (alpha.scalarFDRep heven ⟶
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
  let : Simple (alpha.scalarFDRep heven) := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_simple n heven _
  have hdimension : Module.finrank ℂ (alpha.scalarFDRep heven) = 1 := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_finrank n heven _
  have hnot : ¬ Nonempty (alpha.scalarFDRep heven ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
    unfold PositiveRoot.scalarFDRep
    exact even_scalar_not_trivial heven _
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  have hbound := odd_coset_survival ideal half hcard hproper alpha hsimple witness
    (alpha.scalarFDRep heven)
  rw [removed_scalar_zero ideal half (by omega) hproper (by omega) _ hdimension hnot,
    zero_add] at hbound
  exact (root_scalar_coset_bound alpha heven).trans hbound
end Right

end Schubert.DihedralSplines.HessenbergIdeal
