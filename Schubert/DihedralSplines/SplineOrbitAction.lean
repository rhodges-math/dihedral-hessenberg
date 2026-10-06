import Schubert.DihedralSplines.SplinePieceSection

/-! # The standard group action of geometric dot translation -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- The dot action bundled as the standard action on the spline carrier. -/
@[instance_reducible] def dotMulAction : MulAction (DihedralGroup n) selected.Spline where
  smul := selected.dot hthree
  one_smul := selected.dot_one hthree
  mul_smul := selected.dot_mul hthree

/-- Bundling the dot action preserves the representation's evaluation. -/
theorem dotMulAction_apply (element : DihedralGroup n) (value : selected.Spline) :
    letI := selected.dotMulAction hthree
    element • value = selected.splineRepresentation hthree element value := rfl

end Schubert.Dihedral.RootSubset
