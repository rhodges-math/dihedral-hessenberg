import DihedralHessenberg.Paper.PaperFull
import DihedralHessenberg.Paper.PaperDividedDifference

/-! # Full-root geometric divided differences -/

noncomputable section

namespace Schubert.DihedralSplines.SchubertSpline

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n]

/-- Every positive-root left reflection joins vertices in the full graph. -/
theorem full_edge (alpha : PositiveRoot n) (vertex : DihedralGroup n) :
    (vertex, alpha.reflection * vertex) ∈ (RootSubset.full n).edges := by
  obtain ⟨index, hendpoint⟩ := exists_right_root_of_left_endpoint n vertex alpha.index
  apply ((RootSubset.full n).mem_edges_iff_index _).mpr
  refine ⟨index, ?_, ?_⟩
  · rw [RootSubset.full_indices]
    exact Set.mem_univ index
  · exact hendpoint.symm

/-- The full-root divided difference is defined on every geometric full spline. -/
def difference (value : (HessenbergIdeal.full n hthree).toRootSubset.Spline)
    (alpha : PositiveRoot n) : (HessenbergIdeal.full n hthree).toRootSubset.Spline :=
  (HessenbergIdeal.full n hthree).dividedDifference value alpha
    (fun vertex _ => full_edge alpha vertex)

/-- Its root-form multiple is the exact reflection dot numerator. -/
theorem difference_mul (value : (HessenbergIdeal.full n hthree).toRootSubset.Spline)
    (alpha : PositiveRoot n) (vertex : DihedralGroup n) :
    alpha.form * (difference value alpha : DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex -
        ((RootSubset.full n).dot hthree alpha.reflection value :
          DihedralGroup n → CoordinatePolynomial) vertex :=
  (HessenbergIdeal.full n hthree).dividedDifference_mul value alpha _ vertex

/-- The full divided difference lowers any positive homogeneous degree by one. -/
theorem difference_mem_piece (value : (HessenbergIdeal.full n hthree).toRootSubset.Spline)
    (alpha : PositiveRoot n) (degree : ℕ)
    (hvalue : value ∈ (RootSubset.full n).piece (degree + 1)) :
    difference value alpha ∈ (RootSubset.full n).piece degree :=
  (HessenbergIdeal.full n hthree).dividedDifference_mem_piece value alpha _ degree hvalue

end Schubert.DihedralSplines.SchubertSpline
