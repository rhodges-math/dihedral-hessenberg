import Schubert.DihedralSplines.FamilyBasis
import Schubert.DihedralSplines.PaperGrading
import Schubert.DihedralSplines.HomogeneousTriangularFamily

/-! # Homogeneous projection and degree counts of geometric triangular families -/

noncomputable section

namespace Schubert.DihedralSplines.TriangularFamily

open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

/-- Project each spline to its prescribed inversion degree. -/
def projectedValue (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    ideal.toRootSubset.Spline :=
  ideal.toRootSubset.component hthree (ideal.toRootSubset.length vertex) (family.value vertex)

/-- Each projected vector belongs to its prescribed homogeneous degree piece. -/
theorem projectedValue_mem (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    family.projectedValue vertex ∈ ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) :=
  ideal.toRootSubset.component_mem hthree _ _

/-- Homogeneous projection preserves every upper-support zero. -/
theorem projectedValue_support (family : TriangularFamily ideal)
    (first second : DihedralGroup n) (hnot : ¬ BruhatLE n hthree first second) :
    (family.projectedValue first : DihedralGroup n → CoordinatePolynomial) second = 0 := by
  change MvPolynomial.homogeneousComponent (ideal.toRootSubset.length first)
    ((family.value first : DihedralGroup n → CoordinatePolynomial) second) = 0
  rw [family.support first second hnot, map_zero]

/-- Projection fixes the nonzero minimal-degree diagonal. -/
theorem projectedValue_diagonal (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    (family.projectedValue vertex : DihedralGroup n → CoordinatePolynomial) vertex =
      (family.value vertex : DihedralGroup n → CoordinatePolynomial) vertex := by
  change MvPolynomial.homogeneousComponent (ideal.toRootSubset.length vertex)
    ((family.value vertex : DihedralGroup n → CoordinatePolynomial) vertex) = _
  rw [ideal.length_indexed]
  exact _root_.Schubert.DihedralSplines.IndexedTriangularFamily.projected_diagonal ideal.indexed
    family.backend
    family.backend_support family.backend_diagonal family.backend_bound vertex

/-- The projected homogeneous family is a separate triangular family. -/
def projected (family : TriangularFamily ideal) : TriangularFamily ideal :=
  ofBound family.projectedValue family.projectedValue_support
    (fun vertex => by rw [family.projectedValue_diagonal]; exact family.diagonal vertex)
    (fun vertex current => (family.projectedValue_mem vertex current).totalDegree_le)

/-- The projected family is homogeneous, independently of the family's lower terms. -/
theorem projected_mem (family : TriangularFamily ideal) (vertex : DihedralGroup n) :
    family.projected.value vertex ∈
      ideal.toRootSubset.piece (ideal.toRootSubset.length vertex) :=
  family.projectedValue_mem vertex

end Schubert.DihedralSplines.TriangularFamily
