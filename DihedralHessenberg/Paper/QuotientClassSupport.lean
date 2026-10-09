import DihedralHessenberg.FiniteGroupCharacters.ClassDimension
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.QuotientRepresentation

/-! # Finite support of quotient representation classes -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Quotient degree classes vanish above the selected-root cardinality. -/
theorem piece_class_above (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    (TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = 0 := by
  apply class_zero_of_finrank
  rw [RootSubset.Left.pieceFDRep_finrank]
  exact TriangularFamily.Left.piece_finrank_above (FlowupSpline.family ideal) degree habove

/-- The quotient class series has no coefficient above its top degree. -/
theorem gradedClass_coeff_above (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    PowerSeries.coeff degree (RootSubset.Left.gradedClass ideal.toRootSubset hthree) = 0 := by
  rw [RootSubset.Left.gradedClass_coeff, piece_class_above ideal degree habove]
end Left

namespace Right
/-- Quotient degree classes vanish above the selected-root cardinality. -/
theorem piece_class_above (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    (TauCeti.SplitK0.of (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = 0 := by
  apply class_zero_of_finrank
  rw [RootSubset.Right.pieceFDRep_finrank]
  exact TriangularFamily.Right.piece_finrank_above (FlowupSpline.family ideal) degree habove

/-- The quotient class series has no coefficient above its top degree. -/
theorem gradedClass_coeff_above (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    PowerSeries.coeff degree (RootSubset.Right.gradedClass ideal.toRootSubset hthree) = 0 := by
  rw [RootSubset.Right.gradedClass_coeff, piece_class_above ideal degree habove]
end Right

end Schubert.DihedralSplines.HessenbergIdeal
