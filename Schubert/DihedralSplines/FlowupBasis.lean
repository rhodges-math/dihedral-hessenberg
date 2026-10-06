import Schubert.DihedralSplines.FlowupRecursion
import Schubert.DihedralSplines.FamilyBasis
import Schubert.DihedralSplines.FamilyRank

/-! # Bases and quotient ranks of the constructed geometric flow-up family -/

noncomputable section

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The constructed flow-up spline is homogeneous of its H-inversion degree. -/
theorem homogeneous (vertex : DihedralGroup n) :
    spline ideal vertex ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) :=
  (construct ideal vertex).homogeneous

/-- The whole-spline degree is precisely the H-inversion degree. -/
theorem degree (vertex : DihedralGroup n) :
    ideal.toRootSubset.degree (spline ideal vertex) = ideal.toRootSubset.length vertex :=
  (construct ideal vertex).degree_eq

/-- Constructed flow-up splines vanish outside their Bruhat upper ideal. -/
theorem support (vertex current : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree vertex current) :
    (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current = 0 :=
  (construct ideal vertex).support current hnot

/-- Every constructed flow-up spline has nonzero diagonal. -/
theorem diagonal (vertex : DihedralGroup n) :
    (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 :=
  (construct ideal vertex).diagonal

namespace Left

/-- The recursive splines form a basis for constant polynomial scalars. -/
def basis :
    letI := ideal.toRootSubset.leftAlgebra hthree
    Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline :=
  TriangularFamily.Left.basis (family ideal)

/-- The basis vectors are the recursive splines. -/
theorem basis_apply (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.leftAlgebra hthree
    basis ideal vertex = spline ideal vertex :=
  TriangularFamily.Left.basis_apply (family ideal) vertex

/-- The geometric spline module is free for constant polynomial scalars. -/
theorem free :
    letI := ideal.toRootSubset.leftAlgebra hthree
    Module.Free CoordinatePolynomial ideal.toRootSubset.Spline := by
  let := ideal.toRootSubset.leftAlgebra hthree
  exact Module.Free.of_basis (basis ideal)

/-- No proper subfamily of the recursive splines generates. -/
theorem minimal (vertices : Set (DihedralGroup n)) :
    letI := ideal.toRootSubset.leftAlgebra hthree
    Submodule.span CoordinatePolynomial (spline ideal '' vertices) = ⊤ ↔
      vertices = Set.univ :=
  TriangularFamily.Left.minimal (family ideal) vertices

/-- Every left quotient degree counts exactly the vertices of that H-length. -/
theorem piece_finrank (degree : ℕ) :
    Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) =
      Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} :=
  TriangularFamily.Left.piece_finrank (family ideal) degree

/-- The full left quotient rank polynomial is the H-length sum. -/
theorem rank_eq : HessenbergIdeal.Left.rankPolynomial ideal = ideal.lengthPolynomial :=
  TriangularFamily.Left.rankPolynomial_eq (family ideal)

end Left

namespace Right

/-- The same recursive splines form a basis for orbit polynomial scalars. -/
def basis :
    letI := ideal.toRootSubset.rightAlgebra hthree
    Module.Basis (DihedralGroup n) CoordinatePolynomial ideal.toRootSubset.Spline :=
  TriangularFamily.Right.basis (family ideal)

/-- The orbit-scalar basis vectors are the recursive splines. -/
theorem basis_apply (vertex : DihedralGroup n) :
    letI := ideal.toRootSubset.rightAlgebra hthree
    basis ideal vertex = spline ideal vertex :=
  TriangularFamily.Right.basis_apply (family ideal) vertex

/-- The geometric spline module is free for orbit polynomial scalars. -/
theorem free :
    letI := ideal.toRootSubset.rightAlgebra hthree
    Module.Free CoordinatePolynomial ideal.toRootSubset.Spline := by
  let := ideal.toRootSubset.rightAlgebra hthree
  exact Module.Free.of_basis (basis ideal)

/-- No proper orbit-scalar subfamily of the recursive splines generates. -/
theorem minimal (vertices : Set (DihedralGroup n)) :
    letI := ideal.toRootSubset.rightAlgebra hthree
    Submodule.span CoordinatePolynomial (spline ideal '' vertices) = ⊤ ↔
      vertices = Set.univ :=
  TriangularFamily.Right.minimal (family ideal) vertices

/-- Every right quotient degree counts exactly the vertices of that H-length. -/
theorem piece_finrank (degree : ℕ) :
    Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) =
      Nat.card {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree} :=
  TriangularFamily.Right.piece_finrank (family ideal) degree

/-- The full right quotient rank polynomial is the H-length sum. -/
theorem rank_eq : HessenbergIdeal.Right.rankPolynomial ideal = ideal.lengthPolynomial :=
  TriangularFamily.Right.rankPolynomial_eq (family ideal)

end Right

end Schubert.DihedralSplines.FlowupSpline
