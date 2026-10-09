import DihedralHessenberg.Paper.TriangularFamily
import DihedralHessenberg.Paper.PaperScalarTransport
import DihedralHessenberg.Paper.TriangularBasis

/-! # Geometric triangular families as polynomial bases -/

noncomputable section

namespace Schubert.DihedralSplines.TriangularFamily

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

/-- Evaluation-preserving transport of the family to the indexed spline carrier. -/
def backend (family : TriangularFamily ideal) : DihedralGroup n → HessenbergSpline ideal.indexed :=
  fun vertex => ideal.splineEquiv (family.value vertex)

/-- Root transport preserves the upper support. -/
theorem backend_support (family : TriangularFamily ideal) (first second : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree first second) :
    (family.backend first : DihedralGroup n → CoordinatePolynomial) second = 0 :=
  family.support first second hnot

/-- Root transport preserves the nonzero diagonal. -/
theorem backend_diagonal (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    (family.backend vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 :=
  family.diagonal vertex

/-- Whole-spline degree equality supplies the indexed diagonal bound. -/
theorem backend_bound (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    ((family.backend vertex : DihedralGroup n → CoordinatePolynomial) vertex).totalDegree ≤
      ideal.indexed.length vertex := family.diagonal_bound vertex

namespace Left

/-- The family is a basis for constant polynomial scalars. -/
def basis (family : TriangularFamily ideal) :
    letI := ideal.toRootSubset.leftAlgebra hthree
    Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline := by
  letI := ideal.toRootSubset.leftAlgebra hthree
  exact (hessenbergLeftTriangularBasis ideal.indexed family.backend family.backend_support
    family.backend_diagonal family.backend_bound).map (HessenbergIdeal.Left.splineEquiv ideal).symm

/-- Every basis vector is the corresponding spline. -/
theorem basis_apply (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.leftAlgebra hthree
    basis family vertex = family.value vertex := by
  let := ideal.toRootSubset.leftAlgebra hthree
  change (HessenbergIdeal.Left.splineEquiv ideal).symm
    (hessenbergLeftTriangularBasis ideal.indexed family.backend family.backend_support
      family.backend_diagonal family.backend_bound vertex) = family.value vertex
  rw [hessenbergLeftTriangularBasis_apply]
  exact (HessenbergIdeal.Left.splineEquiv ideal).symm_apply_apply (family.value vertex)

/-- No proper subfamily generates the geometric spline module for constant scalars. -/
theorem minimal (family : TriangularFamily ideal) (vertices : Set (DihedralGroup n)) :
    letI := ideal.toRootSubset.leftAlgebra hthree
    Submodule.span CoordinatePolynomial (family.value '' vertices) = ⊤ ↔
      vertices = Set.univ := by
  let := ideal.toRootSubset.leftAlgebra hthree
  have hvectors : (basis family : DihedralGroup n → ideal.toRootSubset.Spline) = family.value :=
    funext (basis_apply family)
  rw [← hvectors]
  exact basis_span_image_eq_top_iff (basis family) vertices

end Left

namespace Right

/-- The same family is a basis for orbit polynomial scalars. -/
def basis (family : TriangularFamily ideal) :
    letI := ideal.toRootSubset.rightAlgebra hthree
    Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline := by
  letI := ideal.toRootSubset.rightAlgebra hthree
  letI : Algebra CoordinatePolynomial (HessenbergSpline ideal.indexed) :=
    (dihedralReflectionData n hthree).rightAlgebra
      (ideal.indexed.roots : Set (PositiveRootIndex n))
  exact (hessenbergRightTriangularBasis ideal.indexed family.backend family.backend_support
    family.backend_diagonal family.backend_bound).map
    (HessenbergIdeal.Right.splineEquiv ideal).symm

/-- Every orbit-scalar basis vector is again the corresponding spline. -/
theorem basis_apply (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.rightAlgebra hthree
    basis family vertex = family.value vertex := by
  let := ideal.toRootSubset.rightAlgebra hthree
  let : Algebra CoordinatePolynomial (HessenbergSpline ideal.indexed) :=
    (dihedralReflectionData n hthree).rightAlgebra
      (ideal.indexed.roots : Set (PositiveRootIndex n))
  change (HessenbergIdeal.Right.splineEquiv ideal).symm
    (hessenbergRightTriangularBasis ideal.indexed family.backend family.backend_support
      family.backend_diagonal family.backend_bound vertex) = family.value vertex
  rw [hessenbergRightTriangularBasis_apply]
  exact (HessenbergIdeal.Right.splineEquiv ideal).symm_apply_apply (family.value vertex)

/-- No proper subfamily generates the geometric spline module for orbit scalars. -/
theorem minimal (family : TriangularFamily ideal) (vertices : Set (DihedralGroup n)) :
    letI := ideal.toRootSubset.rightAlgebra hthree
    Submodule.span CoordinatePolynomial (family.value '' vertices) = ⊤ ↔
      vertices = Set.univ := by
  let := ideal.toRootSubset.rightAlgebra hthree
  have hvectors : (basis family : DihedralGroup n → ideal.toRootSubset.Spline) = family.value :=
    funext (basis_apply family)
  rw [← hvectors]
  exact basis_span_image_eq_top_iff (basis family) vertices

end Right

end Schubert.DihedralSplines.TriangularFamily
