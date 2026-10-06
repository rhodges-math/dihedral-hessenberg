import Schubert.DihedralSplines.MinimalGeneratorDegrees
import Schubert.DihedralSplines.HomogeneousWholeDegree

/-! # Intrinsic degrees of arbitrary minimal homogeneous generating sets -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- Counts in the whole-spline degree equal the quotient degree dimensions. -/
theorem minimal_degree_count (generators : Set ideal.toRootSubset.Spline)
    (hhomogeneous : ∀ value : generators, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hspan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) (degree : ℕ) :
    Nat.card {value : generators // ideal.toRootSubset.degree value.val = degree} =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := by
  classical
  let := ideal.toRootSubset.leftAlgebra hthree
  let degrees : generators → ℕ := fun value => (hhomogeneous value).choose
  have hvalues : ∀ value : generators,
      value.val ∈ ideal.toRootSubset.piece (degrees value) :=
    fun value => (hhomogeneous value).choose_spec
  have heq : degrees = fun value => ideal.toRootSubset.degree value.val := by
    funext value
    exact (ideal.toRootSubset.homogeneous_degree (hvalues value)
      (minimal_generator_ne_zero generators hspan hminimal value.property)).symm
  have hcounts := generator_degree_count ideal generators degrees hvalues hspan hminimal degree
  simpa only [heq] using hcounts

/-- Any two minimal homogeneous sets have identical intrinsic whole-degree counts. -/
theorem minimal_degrees_eq (first second : Set ideal.toRootSubset.Spline)
    (hfirst : ∀ value : first, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hsecond : ∀ value : second, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hfirstSpan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial first = ⊤)
    (hsecondSpan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial second = ⊤)
    (hfirstMinimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ first, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = first)
    (hsecondMinimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ second, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = second)
    (degree : ℕ) :
    Nat.card {value : first // ideal.toRootSubset.degree value.val = degree} =
      Nat.card {value : second // ideal.toRootSubset.degree value.val = degree} :=
  (minimal_degree_count ideal first hfirst hfirstSpan hfirstMinimal degree).trans
    (minimal_degree_count ideal second hsecond hsecondSpan hsecondMinimal degree).symm

end Left

namespace Right

/-- Counts in the whole-spline degree equal the quotient degree dimensions. -/
theorem minimal_degree_count (generators : Set ideal.toRootSubset.Spline)
    (hhomogeneous : ∀ value : generators, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hspan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) (degree : ℕ) :
    Nat.card {value : generators // ideal.toRootSubset.degree value.val = degree} =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := by
  classical
  let := ideal.toRootSubset.rightAlgebra hthree
  let degrees : generators → ℕ := fun value => (hhomogeneous value).choose
  have hvalues : ∀ value : generators,
      value.val ∈ ideal.toRootSubset.piece (degrees value) :=
    fun value => (hhomogeneous value).choose_spec
  have heq : degrees = fun value => ideal.toRootSubset.degree value.val := by
    funext value
    exact (ideal.toRootSubset.homogeneous_degree (hvalues value)
      (minimal_generator_ne_zero generators hspan hminimal value.property)).symm
  have hcounts := generator_degree_count ideal generators degrees hvalues hspan hminimal degree
  simpa only [heq] using hcounts

/-- Any two minimal homogeneous sets have identical intrinsic whole-degree counts. -/
theorem minimal_degrees_eq (first second : Set ideal.toRootSubset.Spline)
    (hfirst : ∀ value : first, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hsecond : ∀ value : second, ∃ degree, value.val ∈ ideal.toRootSubset.piece degree)
    (hfirstSpan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial first = ⊤)
    (hsecondSpan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial second = ⊤)
    (hfirstMinimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ first, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = first)
    (hsecondMinimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ second, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = second)
    (degree : ℕ) :
    Nat.card {value : first // ideal.toRootSubset.degree value.val = degree} =
      Nat.card {value : second // ideal.toRootSubset.degree value.val = degree} :=
  (minimal_degree_count ideal first hfirst hfirstSpan hfirstMinimal degree).trans
    (minimal_degree_count ideal second hsecond hsecondSpan hsecondMinimal degree).symm

end Right

end Schubert.DihedralSplines.HessenbergIdeal
