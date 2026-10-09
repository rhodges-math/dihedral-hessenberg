import DihedralHessenberg.Splines.HomogeneousAlgebraGenerators
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.PaperCoordinates

/-! # Degree counts of arbitrary minimal homogeneous spline generators -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.Splines
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- Every minimal homogeneous generating set has the quotient degree dimensions. -/
theorem generator_degree_count (generators : Set ideal.toRootSubset.Spline)
    (degrees : generators → ℕ)
    (hhomogeneous : ∀ value : generators, value.val ∈ ideal.toRootSubset.piece (degrees value))
    (hspan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) (degree : ℕ) :
    Nat.card {value : generators // degrees value = degree} =
      Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := by
  classical
  let := ideal.toRootSubset.leftAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial ideal.toRootSubset.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => (ideal.toRootSubset.constantHom hthree).commutes _
  let : GradedAlgebra ideal.toRootSubset.piece := ideal.toRootSubset.gradedAlgebra hthree
  let : GradedAlgebra (RootSubset.Left.piece ideal.toRootSubset hthree) :=
    RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree
  let : DirectSum.Decomposition (RootSubset.Left.piece ideal.toRootSubset hthree) :=
    (RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree).toDecomposition
  have hfinite := minimal_generators_finite (FlowupSpline.Left.basis ideal)
    generators hspan hminimal
  let : Fintype generators := hfinite.fintype
  have hrange : Set.range (Subtype.val : generators → ideal.toRootSubset.Spline) =
      generators := by
    ext value
    simp
  have hindexed : ∀ indices : Set generators,
      Submodule.span CoordinatePolynomial (Subtype.val '' indices) = ⊤ →
        indices = Set.univ := by
    intro indices hgenerate
    have hsubset : (Subtype.val '' indices : Set ideal.toRootSubset.Spline) ⊆ generators := by
      rintro value ⟨other, _, rfl⟩
      exact other.property
    have heq := hminimal _ hsubset hgenerate
    apply Set.eq_univ_of_forall
    intro value
    have hmember : value.val ∈ Subtype.val '' indices := by rw [heq]; exact value.property
    obtain ⟨other, hother, hequal⟩ := hmember
    exact (Subtype.ext hequal) ▸ hother
  let weights := ideal.toRootSubset.length
  have hbasis : ∀ vertex, FlowupSpline.Left.basis ideal vertex ∈
      ideal.toRootSubset.piece (weights vertex) := by
    intro vertex
    rw [FlowupSpline.Left.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hmap : ∀ rowDegree (value : ideal.toRootSubset.Spline),
      value ∈ ideal.toRootSubset.piece rowDegree →
        Ideal.Quotient.mk _ value ∈ RootSubset.Left.piece ideal.toRootSubset hthree rowDegree := by
    intro rowDegree value hvalue
    exact (RootSubset.Left.mem_piece ideal.toRootSubset hthree rowDegree _).2
      ⟨value, hvalue, rfl⟩
  obtain ⟨descended, hdescended⟩ := @minimal_homogeneous_algebra_basis
    ℂ (Fin 2) ideal.toRootSubset.Spline (DihedralGroup n) generators
    _ _ _ _ _ _ _ _ ideal.toRootSubset.piece _
    (FlowupSpline.Left.basis ideal) weights hbasis
    (fun sd vd polynomial value hp hv =>
      RootSubset.Left.smul_mem_piece ideal.toRootSubset hthree sd vd polynomial hp value hv)
    (RootSubset.Left.piece ideal.toRootSubset hthree)
    (RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree).toDecomposition hmap
    (Subtype.val : generators → ideal.toRootSubset.Spline) degrees hhomogeneous
    (hrange.symm ▸ hspan) hindexed (Finset.univ.sup weights)
    (fun vertex => Finset.le_sup (Finset.mem_univ vertex))
  have hdegrees : ∀ value, descended value ∈
      RootSubset.Left.piece ideal.toRootSubset hthree (degrees value) := by
    intro value
    rw [hdescended]
    exact hmap _ _ (hhomogeneous value)
  exact (arbitraryHomogeneousPieceBasis_finrank
    (RootSubset.Left.piece ideal.toRootSubset hthree) descended degrees hdegrees degree).symm

/-- Any two minimal homogeneous generating sets have the same number in every degree. -/
theorem generator_degrees_eq (first second : Set ideal.toRootSubset.Spline)
    (firstDegrees : first → ℕ) (secondDegrees : second → ℕ)
    (hfirst : ∀ value : first, value.val ∈ ideal.toRootSubset.piece (firstDegrees value))
    (hsecond : ∀ value : second, value.val ∈ ideal.toRootSubset.piece (secondDegrees value))
    (hfirstSpan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial first = ⊤)
    (hsecondSpan : letI := ideal.toRootSubset.leftAlgebra hthree
      Submodule.span CoordinatePolynomial second = ⊤)
    (hfirstMinimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ first, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = first)
    (hsecondMinimal : letI := ideal.toRootSubset.leftAlgebra hthree
      ∀ smaller ⊆ second, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = second)
    (degree : ℕ) :
    Nat.card {value : first // firstDegrees value = degree} =
      Nat.card {value : second // secondDegrees value = degree} :=
  (generator_degree_count ideal first firstDegrees hfirst hfirstSpan hfirstMinimal degree).trans
    (generator_degree_count ideal second secondDegrees hsecond hsecondSpan
      hsecondMinimal degree).symm

end Left

namespace Right

/-- Every minimal homogeneous generating set has the quotient degree dimensions. -/
theorem generator_degree_count (generators : Set ideal.toRootSubset.Spline)
    (degrees : generators → ℕ)
    (hhomogeneous : ∀ value : generators, value.val ∈ ideal.toRootSubset.piece (degrees value))
    (hspan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial generators = ⊤)
    (hminimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ generators, Submodule.span CoordinatePolynomial smaller = ⊤ →
        smaller = generators) (degree : ℕ) :
    Nat.card {value : generators // degrees value = degree} =
      Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := by
  classical
  let := ideal.toRootSubset.rightAlgebra hthree
  let : IsScalarTower ℂ CoordinatePolynomial ideal.toRootSubset.Spline :=
    IsScalarTower.of_algebraMap_eq fun _ => ((ideal.toRootSubset.orbitHom hthree).commutes _).symm
  let : GradedAlgebra ideal.toRootSubset.piece := ideal.toRootSubset.gradedAlgebra hthree
  let : GradedAlgebra (RootSubset.Right.piece ideal.toRootSubset hthree) :=
    RootSubset.Right.gradedAlgebra ideal.toRootSubset hthree
  let : DirectSum.Decomposition (RootSubset.Right.piece ideal.toRootSubset hthree) :=
    (RootSubset.Right.gradedAlgebra ideal.toRootSubset hthree).toDecomposition
  have hfinite := minimal_generators_finite (FlowupSpline.Right.basis ideal)
    generators hspan hminimal
  let : Fintype generators := hfinite.fintype
  have hrange : Set.range (Subtype.val : generators → ideal.toRootSubset.Spline) =
      generators := by
    ext value
    simp
  have hindexed : ∀ indices : Set generators,
      Submodule.span CoordinatePolynomial (Subtype.val '' indices) = ⊤ →
        indices = Set.univ := by
    intro indices hgenerate
    have hsubset : (Subtype.val '' indices : Set ideal.toRootSubset.Spline) ⊆ generators := by
      rintro value ⟨other, _, rfl⟩
      exact other.property
    have heq := hminimal _ hsubset hgenerate
    apply Set.eq_univ_of_forall
    intro value
    have hmember : value.val ∈ Subtype.val '' indices := by rw [heq]; exact value.property
    obtain ⟨other, hother, hequal⟩ := hmember
    exact (Subtype.ext hequal) ▸ hother
  let weights := ideal.toRootSubset.length
  have hbasis : ∀ vertex, FlowupSpline.Right.basis ideal vertex ∈
      ideal.toRootSubset.piece (weights vertex) := by
    intro vertex
    rw [FlowupSpline.Right.basis_apply]
    exact FlowupSpline.homogeneous ideal vertex
  have hmap : ∀ rowDegree (value : ideal.toRootSubset.Spline),
      value ∈ ideal.toRootSubset.piece rowDegree →
        Ideal.Quotient.mk _ value ∈ RootSubset.Right.piece ideal.toRootSubset hthree rowDegree := by
    intro rowDegree value hvalue
    exact (RootSubset.Right.mem_piece ideal.toRootSubset hthree rowDegree _).2
      ⟨value, hvalue, rfl⟩
  obtain ⟨descended, hdescended⟩ := @minimal_homogeneous_algebra_basis
    ℂ (Fin 2) ideal.toRootSubset.Spline (DihedralGroup n) generators
    _ _ _ _ _ _ _ _ ideal.toRootSubset.piece _
    (FlowupSpline.Right.basis ideal) weights hbasis
    (fun sd vd polynomial value hp hv =>
      RootSubset.Right.smul_mem_piece ideal.toRootSubset hthree sd vd polynomial hp value hv)
    (RootSubset.Right.piece ideal.toRootSubset hthree)
    (RootSubset.Right.gradedAlgebra ideal.toRootSubset hthree).toDecomposition hmap
    (Subtype.val : generators → ideal.toRootSubset.Spline) degrees hhomogeneous
    (hrange.symm ▸ hspan) hindexed (Finset.univ.sup weights)
    (fun vertex => Finset.le_sup (Finset.mem_univ vertex))
  have hdegrees : ∀ value, descended value ∈
      RootSubset.Right.piece ideal.toRootSubset hthree (degrees value) := by
    intro value
    rw [hdescended]
    exact hmap _ _ (hhomogeneous value)
  exact (arbitraryHomogeneousPieceBasis_finrank
    (RootSubset.Right.piece ideal.toRootSubset hthree) descended degrees hdegrees degree).symm

/-- Any two minimal homogeneous generating sets have the same number in every degree. -/
theorem generator_degrees_eq (first second : Set ideal.toRootSubset.Spline)
    (firstDegrees : first → ℕ) (secondDegrees : second → ℕ)
    (hfirst : ∀ value : first, value.val ∈ ideal.toRootSubset.piece (firstDegrees value))
    (hsecond : ∀ value : second, value.val ∈ ideal.toRootSubset.piece (secondDegrees value))
    (hfirstSpan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial first = ⊤)
    (hsecondSpan : letI := ideal.toRootSubset.rightAlgebra hthree
      Submodule.span CoordinatePolynomial second = ⊤)
    (hfirstMinimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ first, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = first)
    (hsecondMinimal : letI := ideal.toRootSubset.rightAlgebra hthree
      ∀ smaller ⊆ second, Submodule.span CoordinatePolynomial smaller = ⊤ → smaller = second)
    (degree : ℕ) :
    Nat.card {value : first // firstDegrees value = degree} =
      Nat.card {value : second // secondDegrees value = degree} :=
  (generator_degree_count ideal first firstDegrees hfirst hfirstSpan hfirstMinimal degree).trans
    (generator_degree_count ideal second secondDegrees hsecond hsecondSpan
      hsecondMinimal degree).symm

end Right

end Schubert.DihedralSplines.HessenbergIdeal
