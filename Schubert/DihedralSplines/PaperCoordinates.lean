import Schubert.DihedralSplines.PaperGrading
import Schubert.Splines.ScalarEmbeddings

/-! # Coordinate evaluations and graded polynomial scalars -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

/-- Distinct polynomials give distinct constant geometric splines. -/
theorem constantHom_injective : Function.Injective (selected.constantHom hthree) :=
  (selected.backendEquiv hthree).symm.injective.comp
    (Schubert.Splines.ReflectionGraphData.constantHom_injective
      (Schubert.DihedralSplines.dihedralReflectionData n hthree) selected.indices)

/-- Distinct polynomials give distinct orbit geometric splines. -/
theorem orbitHom_injective : Function.Injective (selected.orbitHom hthree) :=
  (selected.backendEquiv hthree).symm.injective.comp
    (Schubert.Splines.ReflectionGraphData.orbitHom_injective
      (Schubert.DihedralSplines.dihedralReflectionData n hthree) selected.indices)

/-- The unit spline is identically the constant polynomial one. -/
theorem one_apply (vertex : DihedralGroup n) :
    ((1 : selected.Spline) : DihedralGroup n → CoordinatePolynomial) vertex = 1 := rfl

/-- The first constant coordinate evaluates to the first polynomial variable. -/
theorem xLeft_apply (vertex : DihedralGroup n) :
    (selected.xLeft hthree : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.X 0 := rfl

/-- The second constant coordinate evaluates to the second polynomial variable. -/
theorem yLeft_apply (vertex : DihedralGroup n) :
    (selected.yLeft hthree : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.X 1 := rfl

/-- The first orbit coordinate is the transformed first polynomial variable. -/
theorem xRight_apply [NeZero n] (vertex : DihedralGroup n) :
    (selected.xRight hthree : DihedralGroup n → CoordinatePolynomial) vertex =
      polynomialAction n vertex (MvPolynomial.X 0) := rfl

/-- The second orbit coordinate is the transformed second polynomial variable. -/
theorem yRight_apply [NeZero n] (vertex : DihedralGroup n) :
    (selected.yRight hthree : DihedralGroup n → CoordinatePolynomial) vertex =
      polynomialAction n vertex (MvPolynomial.X 1) := rfl

/-- Constant polynomial embedding preserves every homogeneous degree. -/
theorem constantHom_mem_piece (degree : ℕ) (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial.IsHomogeneous degree) :
    selected.constantHom hthree polynomial ∈ selected.piece degree := fun _ => hpolynomial

/-- Orbit polynomial embedding preserves every homogeneous degree. -/
theorem orbitHom_mem_piece [NeZero n] (degree : ℕ) (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial.IsHomogeneous degree) :
    selected.orbitHom hthree polynomial ∈ selected.piece degree := fun vertex =>
  polynomialAction_isHomogeneous n vertex hpolynomial

namespace Left

/-- Constant homogeneous polynomial scalars add their degree to a homogeneous spline degree. -/
theorem smul_mem_piece (scalarDegree valueDegree : ℕ) (polynomial : CoordinatePolynomial)
    (hpolynomial : polynomial.IsHomogeneous scalarDegree) (value : selected.Spline)
    (hvalue : value ∈ selected.piece valueDegree) :
    letI := selected.leftAlgebra hthree
    polynomial • value ∈ selected.piece (scalarDegree + valueDegree) := by
  let := selected.leftAlgebra hthree
  intro vertex
  exact hpolynomial.mul (hvalue vertex)

end Left

namespace Right

/-- Orbit homogeneous polynomial scalars add their degree to a homogeneous spline degree. -/
theorem smul_mem_piece [NeZero n] (scalarDegree valueDegree : ℕ)
    (polynomial : CoordinatePolynomial) (hpolynomial : polynomial.IsHomogeneous scalarDegree)
    (value : selected.Spline) (hvalue : value ∈ selected.piece valueDegree) :
    letI := selected.rightAlgebra hthree
    polynomial • value ∈ selected.piece (scalarDegree + valueDegree) := by
  let := selected.rightAlgebra hthree
  intro vertex
  exact (polynomialAction_isHomogeneous n vertex hpolynomial).mul (hvalue vertex)

end Right

end Schubert.Dihedral.RootSubset
