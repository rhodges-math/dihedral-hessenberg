import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.RingTheory.Finiteness.Basic
import DihedralHessenberg.Splines.FinitePolynomialGrading
import DihedralHessenberg.Splines.ReflectionNoetherian
import DihedralHessenberg.Splines.GradedReflectionGraph

/-! # Homogeneous finite generators from an additive decomposition -/

namespace Schubert.Splines

variable {R K M I : Type*} [Semiring R] [Semiring K] [AddCommMonoid M]
variable [Module R M] [Module K M] [DecidableEq I]

/-- A finite module with an internal homogeneous decomposition has homogeneous generators.
The decomposition need not be linear over the scalar ring used for generation. -/
theorem exists_homogeneous_generators (pieces : I → Submodule K M)
    [DirectSum.Decomposition pieces] [Module.Finite R M] :
    ∃ generators : Finset M, Submodule.span R (generators : Set M) = ⊤ ∧
      ∀ value ∈ generators, ∃ degree, value ∈ pieces degree := by
  classical
  obtain ⟨original, horiginal⟩ := Module.Finite.fg_top (R := R) (M := M)
  let indices := Σ value : original, (DirectSum.decompose pieces value.1).support
  let component (index : indices) : M :=
    (DirectSum.decompose pieces index.1.1 index.2).1
  refine ⟨Finset.univ.image component, ?_, ?_⟩
  · rw [← top_le_iff, ← horiginal, Submodule.span_le]
    intro value hvalue
    rw [← DirectSum.sum_support_decompose pieces value]
    apply Submodule.sum_mem
    intro degree hdegree
    apply Submodule.subset_span
    exact Finset.mem_image.mpr ⟨⟨⟨value, hvalue⟩, degree, hdegree⟩,
      Finset.mem_univ _, rfl⟩
  · intro value hvalue
    obtain ⟨index, _, rfl⟩ := Finset.mem_image.mp hvalue
    exact ⟨index.2.1, (DirectSum.decompose pieces index.1.1 index.2).2⟩

end Schubert.Splines

namespace Schubert.Splines.GradedReflectionGraphData

variable {K P W T : Type*} [CommRing K] [IsNoetherianRing K] [Finite P]
variable [Group W] [Fintype W]
variable (data : GradedReflectionGraphData K P W T)

/-- Finite reflection splines have homogeneous generators for the left polynomial scalars. -/
theorem exists_left_homogeneous_generators (selected : Set T) :
    ∃ generators : Finset (data.toReflectionGraphData.Spline selected),
      Submodule.span (MvPolynomial P K)
        (generators : Set (data.toReflectionGraphData.Spline selected)) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree, value ∈ data.homogeneousPiece selected degree := by
  let := data.toReflectionGraphData.leftSpline_finite selected
  let := (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  exact exists_homogeneous_generators
    (data.toReflectionGraphData.reflectionGraph selected).homogeneousPiece

/-- The same grading admits finite generators for the right polynomial scalars. -/
theorem exists_right_homogeneous_generators (selected : Set T) :
    let := data.toReflectionGraphData.rightAlgebra selected
    ∃ generators : Finset (data.toReflectionGraphData.Spline selected),
      Submodule.span (MvPolynomial P K)
        (generators : Set (data.toReflectionGraphData.Spline selected)) = ⊤ ∧
        ∀ value ∈ generators, ∃ degree, value ∈ data.homogeneousPiece selected degree := by
  let := data.toReflectionGraphData.rightAlgebra selected
  let := data.toReflectionGraphData.rightSpline_finite selected
  let := (data.toReflectionGraphData.reflectionGraph selected).gradedAlgebra
    (data.edgeIdeal_homogeneous selected)
  exact exists_homogeneous_generators
    (data.toReflectionGraphData.reflectionGraph selected).homogeneousPiece

end Schubert.Splines.GradedReflectionGraphData
