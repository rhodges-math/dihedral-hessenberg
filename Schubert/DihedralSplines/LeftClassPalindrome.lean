import Schubert.DihedralSplines.QuotientSymmetry

/-! # Palindromicity of the left graded action -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Complementary coefficients of the left class series are equal. -/
theorem class_palindromic (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    PowerSeries.coeff degree (RootSubset.Left.gradedClass ideal.toRootSubset hthree) =
      PowerSeries.coeff (ideal.carrier.ncard - degree)
        (RootSubset.Left.gradedClass ideal.toRootSubset hthree) := by
  rw [RootSubset.Left.gradedClass_coeff, RootSubset.Left.gradedClass_coeff]
  exact TauCeti.SplitK0.of_congr (complementary_iso ideal degree hdegree).some

end Schubert.DihedralSplines.HessenbergIdeal.Left
