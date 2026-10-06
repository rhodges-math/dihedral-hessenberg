import Schubert.DihedralSplines.HessenbergConvolution
import Schubert.Dihedral.PolynomialClass
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Representation-ring convolution of geometric spline degrees -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The degree family of the homogeneous spline actions. -/
def splineGradedRepresentation : GradedRepresentation ℂ (DihedralGroup n) := splineFDRep ideal

/-- The series of the spline degree classes in the standard representation ring. -/
def splineGradedClass : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n)) :=
  gradedClass (splineGradedRepresentation ideal)

namespace Left

/-- The graded spline class is the product of its scalar and quotient classes. -/
theorem spline_class_product : splineGradedClass ideal =
    polynomialGradedClass n *
      RootSubset.Left.gradedClass ideal.toRootSubset hthree := by
  classical
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  simp only [splineGradedClass, polynomialGradedClass, RootSubset.Left.gradedClass,
    gradedClass_coeff]
  change TauCeti.SplitK0.of (splineFDRep ideal degree) = _
  rw [TauCeti.SplitK0.of_congr (degree_tensor_iso ideal degree).some,
    TauCeti.SplitK0.of_biproduct]
  apply Finset.sum_congr rfl
  intro split _
  exact (TauCeti.SplitK0.of_mul_of _ _).symm

end Left

namespace Right

/-- The graded spline class is the product of its scalar and quotient classes. -/
theorem spline_class_product : splineGradedClass ideal =
    gradedClass (RootSubset.Right.scalarPieceFDRep ideal.toRootSubset hthree) *
      RootSubset.Right.gradedClass ideal.toRootSubset hthree := by
  classical
  apply PowerSeries.ext
  intro degree
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← Fin.sum_univ_eq_sum_range]
  simp only [splineGradedClass, RootSubset.Right.gradedClass,
    gradedClass_coeff]
  change TauCeti.SplitK0.of (splineFDRep ideal degree) = _
  rw [TauCeti.SplitK0.of_congr (degree_orbit_tensor_iso ideal degree).some,
    TauCeti.SplitK0.of_biproduct]
  apply Finset.sum_congr rfl
  intro split _
  exact (TauCeti.SplitK0.of_mul_of _ _).symm

end Right

end Schubert.DihedralSplines.HessenbergIdeal
