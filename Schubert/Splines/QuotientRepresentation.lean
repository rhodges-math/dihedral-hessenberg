import Schubert.Splines.QuotientGrading
import Schubert.Splines.QuotientAction
import Mathlib.RepresentationTheory.Basic

/-! # Homogeneous representations on the two spline quotients

The descended dot actions preserve images of homogeneous splines. Restricting their
base-ring linear maps to these pieces uses the standard subrepresentation construction.
-/

namespace Schubert.Splines.GradedReflectionGraphData

universe u v w z

variable {K : Type u} {P : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [Group W]
variable (data : GradedReflectionGraphData K P W T)

/-- Left quotient dot translation preserves each homogeneous quotient piece. -/
theorem leftQuotientDotEquiv_mem_piece (selected : Set T) (element : W) (degree : ℕ)
    (value : data.toReflectionGraphData.LeftQuotient selected)
    (hvalue : value ∈ data.leftQuotientPiece selected degree) :
    data.leftQuotientDotEquiv selected element value ∈
      data.leftQuotientPiece selected degree := by
  obtain ⟨spline, hspline, rfl⟩ :=
    (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).1 hvalue
  rw [data.leftQuotientDotEquiv_mk]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
    (data.dot_mem_homogeneousPiece selected element degree spline hspline)

/-- Right quotient dot translation preserves each homogeneous quotient piece. -/
theorem rightQuotientDotEquiv_mem_piece (selected : Set T) (element : W) (degree : ℕ)
    (value : data.toReflectionGraphData.RightQuotient selected)
    (hvalue : value ∈ data.rightQuotientPiece selected degree) :
    data.rightQuotientDotEquiv selected element value ∈
      data.rightQuotientPiece selected degree := by
  obtain ⟨spline, hspline, rfl⟩ :=
    (TauCeti.GradedAlgebra.mem_quotientPiece_iff _ _).1 hvalue
  rw [data.rightQuotientDotEquiv_mk]
  exact TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _
    (data.dot_mem_homogeneousPiece selected element degree spline hspline)

/-- The base-ring linear dot representation on the whole left quotient. -/
noncomputable def leftQuotientRepresentation (selected : Set T) :
    Representation K W (data.toReflectionGraphData.LeftQuotient selected) :=
  (AlgEquiv.toLinearMapHom K _).comp (data.leftQuotientDotAction selected)

/-- The base-ring linear dot representation on the whole right quotient. -/
noncomputable def rightQuotientRepresentation (selected : Set T) :
    Representation K W (data.toReflectionGraphData.RightQuotient selected) :=
  (AlgEquiv.toLinearMapHom K _).comp (data.rightQuotientDotAction selected)

/-- The dot representation on a homogeneous piece of the left quotient. -/
noncomputable def leftQuotientPieceRepresentation (selected : Set T) (degree : ℕ) :
    Representation K W (data.leftQuotientPiece selected degree) :=
  (data.leftQuotientRepresentation selected).subrepresentation
    (data.leftQuotientPiece selected degree) fun element value hvalue =>
      data.leftQuotientDotEquiv_mem_piece selected element degree value hvalue

/-- The dot representation on a homogeneous piece of the right quotient. -/
noncomputable def rightQuotientPieceRepresentation (selected : Set T) (degree : ℕ) :
    Representation K W (data.rightQuotientPiece selected degree) :=
  (data.rightQuotientRepresentation selected).subrepresentation
    (data.rightQuotientPiece selected degree) fun element value hvalue =>
      data.rightQuotientDotEquiv_mem_piece selected element degree value hvalue

end Schubert.Splines.GradedReflectionGraphData
