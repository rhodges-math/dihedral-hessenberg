import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.HessenbergLongest
import DihedralHessenberg.Dihedral.BruhatOrder

/-! # Downward partners of the flow-up splines -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Longest translation of the complementary flow-up vector. -/
def opposite (vertex : DihedralGroup n) : ideal.toRootSubset.Spline :=
  ideal.toRootSubset.dot hthree (longestElement n hthree)
    (spline ideal (longestElement n hthree * vertex))

/-- The downward partner has the complementary Hessenberg degree. -/
theorem opposite_homogeneous (vertex : DihedralGroup n) :
    opposite ideal vertex ∈ ideal.toRootSubset.piece
      (ideal.carrier.ncard - ideal.toRootSubset.length vertex) := by
  have hdegree := ideal.length_longest_add vertex
  have heq : ideal.toRootSubset.length (longestElement n hthree * vertex) =
      ideal.carrier.ncard - ideal.toRootSubset.length vertex := by omega
  unfold opposite
  rw [← heq]
  exact ideal.toRootSubset.dot_mem_piece hthree _ _ _ (homogeneous ideal _)

/-- Downward partners vanish away from the Bruhat lower ideal. -/
theorem opposite_support (vertex current : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree current vertex) :
    (opposite ideal vertex : DihedralGroup n → CoordinatePolynomial) current = 0 := by
  have hinverse : (longestElement n hthree)⁻¹ = longestElement n hthree :=
    alternatingWord_top_inv n hthree
  rw [opposite, RootSubset.dot_apply, hinverse]
  rw [support ideal _ _ (fun h => hnot ((bruhat_longest_mul n hthree vertex current).mp h))]
  exact map_zero _

/-- Downward partners have nonzero diagonal values. -/
theorem opposite_diagonal (vertex : DihedralGroup n) :
    (opposite ideal vertex : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
  have hinverse : (longestElement n hthree)⁻¹ = longestElement n hthree :=
    alternatingWord_top_inv n hthree
  rw [opposite, RootSubset.dot_apply, hinverse]
  exact fun h => diagonal ideal _ ((polynomialAction n _).injective
    (h.trans (map_zero _).symm))

/-- Products of upward and downward partners vanish unless their indices are ordered. -/
theorem opposite_product_zero (first second : DihedralGroup n)
    (hnot : ¬ BruhatLE n hthree first second) :
    spline ideal first * opposite ideal second = 0 := by
  apply Subtype.ext
  funext current
  change (spline ideal first : DihedralGroup n → CoordinatePolynomial) current *
    (opposite ideal second : DihedralGroup n → CoordinatePolynomial) current = 0
  by_cases hfirst : BruhatLE n hthree first current
  · have hsecond : ¬ BruhatLE n hthree current second :=
      fun h => hnot ((bruhatPartialOrder n hthree).le_trans first current second hfirst h)
    rw [opposite_support ideal second current hsecond, mul_zero]
  · rw [support ideal first current hfirst, zero_mul]

/-- Matched products are supported at precisely their common indexing vertex. -/
theorem opposite_product_support (vertex current : DihedralGroup n) (hne : current ≠ vertex) :
    (spline ideal vertex * opposite ideal vertex :
      DihedralGroup n → CoordinatePolynomial) current = 0 := by
  change (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current *
    (opposite ideal vertex : DihedralGroup n → CoordinatePolynomial) current = 0
  by_cases hfirst : BruhatLE n hthree vertex current
  · have hsecond : ¬ BruhatLE n hthree current vertex :=
      fun h => hne ((bruhatPartialOrder n hthree).le_antisymm current vertex h hfirst)
    rw [opposite_support ideal vertex current hsecond, mul_zero]
  · rw [support ideal vertex current hfirst, zero_mul]

/-- Matched products have nonzero diagonal. -/
theorem opposite_product_diagonal (vertex : DihedralGroup n) :
    (spline ideal vertex * opposite ideal vertex :
      DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 :=
  mul_ne_zero (diagonal ideal vertex) (opposite_diagonal ideal vertex)

/-- Matched products have the top homogeneous degree. -/
theorem opposite_product_homogeneous (vertex : DihedralGroup n) :
    spline ideal vertex * opposite ideal vertex ∈ ideal.toRootSubset.piece ideal.carrier.ncard := by
  have hdegree := ideal.length_longest_add vertex
  have hsum : ideal.toRootSubset.length vertex +
      (ideal.carrier.ncard - ideal.toRootSubset.length vertex) = ideal.carrier.ncard := by omega
  intro current
  change MvPolynomial.IsHomogeneous
    ((spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current *
      (opposite ideal vertex : DihedralGroup n → CoordinatePolynomial) current) _
  rw [← hsum]
  exact (homogeneous ideal vertex current).mul (opposite_homogeneous ideal vertex current)

end Schubert.DihedralSplines.FlowupSpline
