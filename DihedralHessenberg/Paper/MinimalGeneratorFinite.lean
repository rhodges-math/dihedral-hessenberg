import DihedralHessenberg.Paper.MinimalHomogeneousDegrees

/-! # Minimal generating sets of spline modules are finite

A generating set of the spline module, for either polynomial structure, that is minimal under
inclusion is finite. Together with `Left.minimal_degrees_eq` and `Right.minimal_degrees_eq`, any two
minimal homogeneous generating sets therefore have the same finite number of elements in each
degree.
-/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- A minimal generating set for the constant polynomial structure is finite. -/
theorem minimal_finite (generators : Set ideal.toRootSubset.Spline)
    (hspan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) :
    generators.Finite := by
  let := ideal.toRootSubset.leftAlgebra hthree
  exact minimal_generators_finite (FlowupSpline.Left.basis ideal) generators hspan hminimal

end Left

namespace Right

/-- A minimal generating set for the orbit polynomial structure is finite. -/
theorem minimal_finite (generators : Set ideal.toRootSubset.Spline)
    (hspan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) :
    generators.Finite := by
  let := ideal.toRootSubset.rightAlgebra hthree
  exact minimal_generators_finite (FlowupSpline.Right.basis ideal) generators hspan hminimal

end Right

end Schubert.DihedralSplines.HessenbergIdeal
