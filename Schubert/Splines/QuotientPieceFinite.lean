import Schubert.Splines.PolynomialSplineFinite
import Schubert.Splines.QuotientGrading

/-! # Finite homogeneous quotient pieces without a polynomial basis hypothesis -/

namespace Schubert.Splines.GradedReflectionGraphData

variable {K P W T : Type*} [CommRing K] [IsNoetherianRing K]
variable [Finite P] [Group W] [Fintype W]
variable (data : GradedReflectionGraphData K P W T)

/-- Each left quotient degree piece is finite on a finite polynomial reflection graph. -/
theorem leftQuotientPiece_finite (selected : Set T) (degree : ℕ) :
    Module.Finite K (data.leftQuotientPiece selected degree) := by
  apply Module.Finite.of_fg
  exact (Module.Finite.iff_fg.mp
    ((data.toReflectionGraphData.reflectionGraph selected).homogeneousPiece_finite degree)).map
    (Ideal.Quotient.mkₐ K (data.toReflectionGraphData.leftVariableIdeal selected)).toLinearMap

/-- Each right quotient degree piece is finite on a finite polynomial reflection graph. -/
theorem rightQuotientPiece_finite (selected : Set T) (degree : ℕ) :
    Module.Finite K (data.rightQuotientPiece selected degree) := by
  apply Module.Finite.of_fg
  exact (Module.Finite.iff_fg.mp
    ((data.toReflectionGraphData.reflectionGraph selected).homogeneousPiece_finite degree)).map
    (Ideal.Quotient.mkₐ K (data.toReflectionGraphData.rightVariableIdeal selected)).toLinearMap

end Schubert.Splines.GradedReflectionGraphData
