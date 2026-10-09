import DihedralHessenberg.Splines.Quotient
import DihedralHessenberg.Splines.GradedReflectionGraph
import DihedralHessenberg.Splines.FinitePolynomialGrading
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient

/-! # Grading the two polynomial spline quotients

Coordinate spline generators are homogeneous, so their extension ideals are homogeneous.
For finitely many vertices the spline algebra is a direct sum of its polynomial degree pieces;
the images of these pieces supply each quotient grading through the pinned quotient API.
-/

namespace Schubert.Splines.GradedReflectionGraphData

universe u v w z

variable {K : Type u} {P : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [Group W] [Fintype W]
variable (data : GradedReflectionGraphData K P W T)

/-- The left coordinate extension ideal is homogeneous in the spline grading. -/
theorem leftVariableIdeal_homogeneous (selected : Set T) :
    letI : GradedAlgebra (data.homogeneousPiece selected) :=
      (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
      (data.edgeIdeal_homogeneous selected)
    (data.toReflectionGraphData.leftVariableIdeal selected).IsHomogeneous
      (data.homogeneousPiece selected) := by
  let : GradedAlgebra (data.homogeneousPiece selected) :=
      (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  rw [ReflectionGraphData.leftVariableIdeal_eq_span]
  apply Ideal.homogeneous_span (data.homogeneousPiece selected)
  rintro value ⟨coordinate, rfl⟩
  refine ⟨1, ?_⟩
  intro vertex
  exact MvPolynomial.isHomogeneous_X K coordinate

/-- The right coordinate extension ideal is homogeneous in the spline grading. -/
theorem rightVariableIdeal_homogeneous (selected : Set T) :
    letI : GradedAlgebra (data.homogeneousPiece selected) :=
      (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
      (data.edgeIdeal_homogeneous selected)
    (data.toReflectionGraphData.rightVariableIdeal selected).IsHomogeneous
      (data.homogeneousPiece selected) := by
  let : GradedAlgebra (data.homogeneousPiece selected) :=
      (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  rw [ReflectionGraphData.rightVariableIdeal_eq_span]
  apply Ideal.homogeneous_span (data.homogeneousPiece selected)
  rintro value ⟨coordinate, rfl⟩
  refine ⟨1, ?_⟩
  intro vertex
  exact data.action_homogeneous vertex 1 (MvPolynomial.X coordinate)
    (MvPolynomial.isHomogeneous_X K coordinate)

/-- The degree piece of the left quotient is the image of the spline degree piece. -/
noncomputable def leftQuotientPiece (selected : Set T) (degree : ℕ) :
    Submodule K (data.toReflectionGraphData.LeftQuotient selected) :=
  TauCeti.GradedAlgebra.quotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.leftVariableIdeal selected) degree

/-- The degree piece of the right quotient is the image of the spline degree piece. -/
noncomputable def rightQuotientPiece (selected : Set T) (degree : ℕ) :
    Submodule K (data.toReflectionGraphData.RightQuotient selected) :=
  TauCeti.GradedAlgebra.quotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.rightVariableIdeal selected) degree

/-- The quotient images of homogeneous splines grade the left quotient algebra. -/
@[instance_reducible]
noncomputable def leftQuotientGradedAlgebra (selected : Set T) :
    GradedAlgebra (data.leftQuotientPiece selected) := by
  let : GradedAlgebra (data.homogeneousPiece selected) :=
    (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  exact TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.leftVariableIdeal selected)
    (data.leftVariableIdeal_homogeneous selected)

/-- The quotient images of homogeneous splines grade the right quotient algebra. -/
@[instance_reducible]
noncomputable def rightQuotientGradedAlgebra (selected : Set T) :
    GradedAlgebra (data.rightQuotientPiece selected) := by
  let : GradedAlgebra (data.homogeneousPiece selected) :=
    (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  exact TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece (data.homogeneousPiece selected)
    (data.toReflectionGraphData.rightVariableIdeal selected)
    (data.rightVariableIdeal_homogeneous selected)

end Schubert.Splines.GradedReflectionGraphData
