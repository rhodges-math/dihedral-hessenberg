import Schubert.DihedralSplines.SchubertDiagonal
import Schubert.DihedralSplines.HomogeneousFamily
import Schubert.DihedralSplines.FamilyBasis

/-! # Homogeneous Schubert bases -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral

variable (n : ℕ) (hthree : 3 ≤ n) [NeZero n]

/-- The Schubert spline has whole degree equal to its canonical vertex length. -/
theorem degree (vertex : DihedralGroup n) :
    (HessenbergIdeal.full n hthree).toRootSubset.degree (spline n hthree vertex) =
      length n hthree vertex :=
  ((construct n hthree vertex).degree_eq).trans (RootSubset.length_full n hthree vertex)

/-- The Schubert functions form a basis for constant polynomial scalars. -/
theorem left_basis :
    letI := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
    ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial
        (HessenbergIdeal.full n hthree).toRootSubset.Spline,
      ∀ vertex, vectors vertex = spline n hthree vertex := by
  let := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
  exact ⟨TriangularFamily.Left.basis (family n hthree),
    TriangularFamily.Left.basis_apply (family n hthree)⟩

/-- The same Schubert functions form a basis for orbit polynomial scalars. -/
theorem right_basis :
    letI := (HessenbergIdeal.full n hthree).toRootSubset.rightAlgebra hthree
    ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial
        (HessenbergIdeal.full n hthree).toRootSubset.Spline,
      ∀ vertex, vectors vertex = spline n hthree vertex := by
  let := (HessenbergIdeal.full n hthree).toRootSubset.rightAlgebra hthree
  exact ⟨TriangularFamily.Right.basis (family n hthree),
    TriangularFamily.Right.basis_apply (family n hthree)⟩

/-- The constant-scalar Schubert basis is homogeneous with the exact displayed degrees. -/
theorem homogeneous_basis :
    letI := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
    ∃ vectors : Module.Basis (DihedralGroup n) CoordinatePolynomial
        (HessenbergIdeal.full n hthree).toRootSubset.Spline,
      (∀ vertex, vectors vertex = spline n hthree vertex) ∧
      ∀ vertex, vectors vertex ∈ (RootSubset.full n).piece (length n hthree vertex) ∧
        (RootSubset.full n).degree (vectors vertex) = length n hthree vertex := by
  let := (HessenbergIdeal.full n hthree).toRootSubset.leftAlgebra hthree
  obtain ⟨vectors, hvectors⟩ := left_basis n hthree
  refine ⟨vectors, hvectors, ?_⟩
  intro vertex
  rw [hvectors]
  exact ⟨homogeneous n hthree vertex, degree n hthree vertex⟩

end Schubert.DihedralSplines.SchubertSpline
