import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Lean.Elab.Tactic.Omega
import DihedralHessenberg.Splines.EdgeDivisibility

/-! # Degree bounds and diagonal divisibility for polynomial splines

A nonzero multiple with no larger total degree is associated to its divisor over a
field. Thus an incident-label product dividing a nonzero diagonal, with the same
degree bound, makes that diagonal divide every spline value forced by those labels.
-/

namespace Schubert.Splines

universe u v w z

variable {K : Type u} {T : Type v} [Field K]

/-- A nonzero polynomial multiple of no larger degree differs from its divisor by a unit. -/
theorem _root_.Schubert.Splines.PolynomialDegree.associated_of_dvd_degree_le
    {divisor multiple : MvPolynomial T K} (hdivides : divisor ∣ multiple)
    (hnonzero : multiple ≠ 0) (hdegree : multiple.totalDegree ≤ divisor.totalDegree) :
    Associated divisor multiple := by
  obtain ⟨factor, rfl⟩ := hdivides
  have hdivisor : divisor ≠ 0 := left_ne_zero_of_mul hnonzero
  have hfactor : factor ≠ 0 := right_ne_zero_of_mul hnonzero
  rw [MvPolynomial.totalDegree_mul_of_isDomain hdivisor hfactor] at hdegree
  have hzeroDegree : factor.totalDegree = 0 := by omega
  have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzeroDegree
  have hcoefficient : factor.coeff 0 ≠ 0 := by
    intro hzero
    apply hfactor
    rw [hconstant, hzero, map_zero]
  apply associated_mul_unit_right
  rw [hconstant]
  exact (isUnit_iff_ne_zero.mpr hcoefficient).map MvPolynomial.C

namespace IdealLabeledGraph

variable {V : Type w} {E : Type z}
variable (graph : IdealLabeledGraph (MvPolynomial T K) V E)

/-- A nonzero diagonal of minimal possible degree divides values with the same edge zeros. -/
theorem diagonal_dvd_of_edge_degree_bound
    (diagonal value : graph.Spline) (vertex : V) (edges : Finset E)
    (labels : E → MvPolynomial T K)
    (hsource : ∀ edge ∈ edges, graph.source edge = vertex)
    (hlabels : ∀ edge ∈ edges, graph.label edge = Ideal.span {labels edge})
    (hrelPrime : (edges : Set E).Pairwise (fun first second =>
      IsRelPrime (labels first) (labels second)))
    (hdiagonalZero : ∀ edge ∈ edges,
      (diagonal : V → MvPolynomial T K) (graph.target edge) = 0)
    (hvalueZero : ∀ edge ∈ edges,
      (value : V → MvPolynomial T K) (graph.target edge) = 0)
    (hnonzero : (diagonal : V → MvPolynomial T K) vertex ≠ 0)
    (hdegree : ((diagonal : V → MvPolynomial T K) vertex).totalDegree ≤
      (∏ edge ∈ edges, labels edge).totalDegree) :
    (diagonal : V → MvPolynomial T K) vertex ∣ (value : V → MvPolynomial T K) vertex := by
  have hdiagonal := graph.prod_labels_dvd_of_targets_eq_zero diagonal vertex edges labels
    hsource hlabels hrelPrime hdiagonalZero
  have hvalue := graph.prod_labels_dvd_of_targets_eq_zero value vertex edges labels
    hsource hlabels hrelPrime hvalueZero
  exact (_root_.Schubert.Splines.PolynomialDegree.associated_of_dvd_degree_le hdiagonal hnonzero
    hdegree).symm.dvd.trans
    hvalue

end IdealLabeledGraph

end Schubert.Splines
