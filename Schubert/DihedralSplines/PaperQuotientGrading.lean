import Schubert.DihedralSplines.PaperGrading
import Schubert.DihedralSplines.PaperQuotient
import Schubert.Splines.QuotientGrading

/-! # Graded coordinate quotients of geometric splines -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- The spline equivalence maps a homogeneous piece onto its corresponding piece. -/
theorem piece_map_backend (degree : ℕ) :
    (selected.piece degree).map (selected.backendEquiv hthree).toLinearMap =
      (dihedralGradedReflectionData n hthree).homogeneousPiece selected.indices degree := by
  rw [selected.piece_backend hthree]
  exact Submodule.map_comap_eq_of_surjective (selected.backendEquiv hthree).surjective _

namespace Left

/-- The coordinate ideal is homogeneous for the pointwise spline grading. -/
theorem ideal_homogeneous :
    letI := selected.gradedAlgebra hthree
    (ideal selected hthree).IsHomogeneous selected.piece := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  rw [ideal_range]
  apply Ideal.homogeneous_span selected.piece
  rintro value ⟨coordinate, rfl⟩
  refine ⟨1, ?_⟩
  intro vertex
  exact MvPolynomial.isHomogeneous_X ℂ coordinate

/-- A quotient degree piece is the image of the corresponding geometric spline piece. -/
def piece (degree : ℕ) : Submodule ℂ (Quotient selected hthree) :=
  (selected.piece degree).map (quotientMap selected hthree).toLinearMap

/-- Degree-piece membership has a homogeneous geometric spline representative. -/
theorem mem_piece (degree : ℕ) (value : Quotient selected hthree) :
    value ∈ piece selected hthree degree ↔ ∃ original ∈ selected.piece degree,
      quotientMap selected hthree original = value := Submodule.mem_map

/-- The coordinate quotient carries the descended homogeneous grading. -/
@[instance_reducible]
def gradedAlgebra : GradedAlgebra (piece selected hthree) := by
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  exact TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece selected.piece
    (ideal selected hthree) (ideal_homogeneous selected hthree)

/-- The quotient equivalence preserves each homogeneous degree piece. -/
theorem piece_backend (degree : ℕ) :
    (piece selected hthree degree).map (backendEquiv selected hthree).toLinearMap =
      (dihedralGradedReflectionData n hthree).leftQuotientPiece selected.indices degree := by
  change ((selected.piece degree).map (quotientMap selected hthree).toLinearMap).map _ = _
  rw [← Submodule.map_comp]
  have hmaps : (backendEquiv selected hthree).toLinearMap.comp
      (quotientMap selected hthree).toLinearMap =
      (Ideal.Quotient.mkₐ ℂ
        ((dihedralReflectionData n hthree).leftVariableIdeal selected.indices)).toLinearMap.comp
        (selected.backendEquiv hthree).toLinearMap := by
    ext value
    rfl
  rw [hmaps, Submodule.map_comp, selected.piece_map_backend hthree]
  rfl

/-- The evaluation-preserving quotient equivalence restricts to each homogeneous piece. -/
def pieceEquiv (degree : ℕ) : piece selected hthree degree ≃ₗ[ℂ]
    (dihedralGradedReflectionData n hthree).leftQuotientPiece selected.indices degree :=
  ((backendEquiv selected hthree).toLinearEquiv.submoduleMap
    (piece selected hthree degree)).trans
    (LinearEquiv.ofEq _ _ (piece_backend selected hthree degree))

end Left

namespace Right

/-- The coordinate ideal is homogeneous for the pointwise spline grading. -/
theorem ideal_homogeneous :
    letI := selected.gradedAlgebra hthree
    (ideal selected hthree).IsHomogeneous selected.piece := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  rw [ideal_range]
  apply Ideal.homogeneous_span selected.piece
  rintro value ⟨coordinate, rfl⟩
  refine ⟨1, ?_⟩
  intro vertex
  exact polynomialAction_isHomogeneous n vertex (MvPolynomial.isHomogeneous_X ℂ coordinate)

/-- A quotient degree piece is the image of the corresponding geometric spline piece. -/
def piece (degree : ℕ) : Submodule ℂ (Quotient selected hthree) :=
  (selected.piece degree).map (quotientMap selected hthree).toLinearMap

/-- Degree-piece membership has a homogeneous geometric spline representative. -/
theorem mem_piece (degree : ℕ) (value : Quotient selected hthree) :
    value ∈ piece selected hthree degree ↔ ∃ original ∈ selected.piece degree,
      quotientMap selected hthree original = value := Submodule.mem_map

/-- The coordinate quotient carries the descended homogeneous grading. -/
@[instance_reducible]
def gradedAlgebra : GradedAlgebra (piece selected hthree) := by
  let : GradedAlgebra selected.piece := selected.gradedAlgebra hthree
  exact TauCeti.GradedAlgebra.gradedAlgebraQuotientPiece selected.piece
    (ideal selected hthree) (ideal_homogeneous selected hthree)

/-- The quotient equivalence preserves each homogeneous degree piece. -/
theorem piece_backend (degree : ℕ) :
    (piece selected hthree degree).map (backendEquiv selected hthree).toLinearMap =
      (dihedralGradedReflectionData n hthree).rightQuotientPiece selected.indices degree := by
  change ((selected.piece degree).map (quotientMap selected hthree).toLinearMap).map _ = _
  rw [← Submodule.map_comp]
  have hmaps : (backendEquiv selected hthree).toLinearMap.comp
      (quotientMap selected hthree).toLinearMap =
      (Ideal.Quotient.mkₐ ℂ
        ((dihedralReflectionData n hthree).rightVariableIdeal selected.indices)).toLinearMap.comp
        (selected.backendEquiv hthree).toLinearMap := by
    ext value
    rfl
  rw [hmaps, Submodule.map_comp, selected.piece_map_backend hthree]
  rfl

/-- The evaluation-preserving quotient equivalence restricts to each homogeneous piece. -/
def pieceEquiv (degree : ℕ) : piece selected hthree degree ≃ₗ[ℂ]
    (dihedralGradedReflectionData n hthree).rightQuotientPiece selected.indices degree :=
  ((backendEquiv selected hthree).toLinearEquiv.submoduleMap
    (piece selected hthree degree)).trans
    (LinearEquiv.ofEq _ _ (piece_backend selected hthree degree))

end Right

end Schubert.Dihedral.RootSubset
