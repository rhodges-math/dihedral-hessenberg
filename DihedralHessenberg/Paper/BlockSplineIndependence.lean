import DihedralHessenberg.Paper.BlockTransport
import DihedralHessenberg.Paper.AdmissibleIndependence

/-! # Independence of homogeneous splines on distinct blocks -/

set_option maxHeartbeats 600000

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Distinct short-block supports make arbitrary localized splines independent. -/
theorem block_splines_independent {I : Type*} [Fintype I]
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      length n hthree alpha.reflection ≤ 2 * half + 1 → alpha.val ∈ ideal)
    (blocks : I → Block ideal) (hhalf : ∀ index, (blocks index).half = half)
    (hinjective : Function.Injective (fun index => (blocks index).vertices))
    (value : I → ideal.toRootSubset.Spline)
    (hhomogeneous : ∀ index, value index ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots ((blocks index).vertices : Set (DihedralGroup n))
        (blocks index).base).card))
    (hsupport : ∀ index vertex, vertex ∉ (blocks index).vertices →
      (value index : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : ∀ index, value index ≠ 0) : LinearIndependent ℂ value := by
  classical
  let coefficient : I → DihedralGroup n → ℂ := fun index => Classical.choose
    ((blocks index).localized_function (value index) (hhomogeneous index)
      (hsupport index) (hnonzero index))
  have hcoefficient : ∀ index vertex, vertex ∈ (blocks index).vertices →
      coefficient index vertex ≠ 0 := fun index => (Classical.choose_spec
    ((blocks index).localized_function (value index) (hhomogeneous index)
      (hsupport index) (hnonzero index))).1
  have hblocks : ∀ index, (∃ base, (blocks index).vertices =
      alternatingBlock base (simpleRoot n hthree 0) (simpleRoot n hthree 1) half) ∨
      (∃ base, (blocks index).vertices =
        alternatingBlock base (simpleRoot n hthree 1) (simpleRoot n hthree 0) half) := by
    intro index
    rcases (blocks index).pair with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Or.inl ⟨(blocks index).base, by
        simp only [Block.vertices, hfirst, hsecond, hhalf index]⟩
    · exact Or.inr ⟨(blocks index).base, by
        simp only [Block.vertices, hfirst, hsecond, hhalf index]⟩
  have hindependent := ideal.toRootSubset.subfamily_independent half hbound hselected
    (fun index => (blocks index).vertices) hinjective hblocks coefficient hcoefficient
  apply LinearIndependent.of_comp ideal.toRootSubset.splineAlgebra.val.toLinearMap
  have heq : (fun index => (value index : DihedralGroup n → CoordinatePolynomial)) =
      (fun index => ideal.toRootSubset.boundaryFunction
        ((blocks index).vertices : Set (DihedralGroup n)) (coefficient index)) := by
    funext index vertex
    simpa only [RootSubset.boundaryFunction, coefficient, Finset.mem_coe] using
      (Classical.choose_spec ((blocks index).localized_function (value index)
      (hhomogeneous index) (hsupport index) (hnonzero index))).2 vertex
  change LinearIndependent ℂ (fun index =>
    (value index : DihedralGroup n → CoordinatePolynomial))
  rw [heq]
  exact hindependent
/-- Distinct admissible supports make boundary-degree splines independent
for proper odd H. -/
theorem odd_block_splines_independent {I : Type*} [Fintype I]
    (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (blocks : I → Block ideal) (hhalf : ∀ index, (blocks index).half = half)
    (hinjective : Function.Injective (fun index => (blocks index).vertices))
    (value : I → ideal.toRootSubset.Spline)
    (hhomogeneous : ∀ index, value index ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots ((blocks index).vertices : Set (DihedralGroup n))
        (blocks index).base).card))
    (hsupport : ∀ index vertex, vertex ∉ (blocks index).vertices →
      (value index : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : ∀ index, value index ≠ 0) : LinearIndependent ℂ value := by
  classical
  let coefficient : I → DihedralGroup n → ℂ := fun index => Classical.choose
    ((blocks index).localized_function (value index) (hhomogeneous index)
      (hsupport index) (hnonzero index))
  have hcoefficient : ∀ index vertex, vertex ∈ (blocks index).vertices →
      coefficient index vertex ≠ 0 := fun index => (Classical.choose_spec
    ((blocks index).localized_function (value index) (hhomogeneous index)
      (hsupport index) (hnonzero index))).1
  have hblocks : ∀ index, (∃ base, (blocks index).vertices =
      alternatingBlock base (simpleRoot n hthree 0) (simpleRoot n hthree 1) half) ∨
      (∃ base, (blocks index).vertices =
        alternatingBlock base (simpleRoot n hthree 1) (simpleRoot n hthree 0) half) := by
    intro index
    rcases (blocks index).pair with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · exact Or.inl ⟨(blocks index).base, by
        simp only [Block.vertices, hfirst, hsecond, hhalf index]⟩
    · exact Or.inr ⟨(blocks index).base, by
        simp only [Block.vertices, hfirst, hsecond, hhalf index]⟩
  have hbound : 2 * half + 1 < n := by
    have hlt := ideal.card_lt hproper
    omega
  obtain ⟨larger, delta, _, hmissing, hcarrier, hprefix⟩ :=
    ideal.odd_extension half hcard hproper
  have hshort : ∀ alpha : PositiveRoot n,
      length n hthree alpha.reflection ≤ 2 * half + 1 → alpha.val ∈ larger.toRootSubset := by
    intro alpha hlength
    change alpha.val ∈ larger.carrier
    rw [hprefix]
    change length n hthree (rootReflection alpha.index) ≤ _ at hlength
    rw [length_rootReflection] at hlength
    exact ⟨alpha.index, by change alpha.index.val < 2 * half + 2; omega, alpha.index_val⟩
  have hindependent := ideal.toRootSubset.independent_of_insert larger.toRootSubset delta
    hmissing hcarrier (fun index => ((blocks index).vertices : Set (DihedralGroup n))) coefficient
    (fun index vertex hvertex => (blocks index).excluded_leaves delta hmissing vertex hvertex)
    (larger.toRootSubset.subfamily_independent half hbound hshort
      (fun index => (blocks index).vertices) hinjective hblocks coefficient hcoefficient)
  apply LinearIndependent.of_comp ideal.toRootSubset.splineAlgebra.val.toLinearMap
  have heq : (fun index => (value index : DihedralGroup n → CoordinatePolynomial)) =
      (fun index => ideal.toRootSubset.boundaryFunction
        ((blocks index).vertices : Set (DihedralGroup n)) (coefficient index)) := by
    funext index vertex
    simpa only [RootSubset.boundaryFunction, coefficient, Finset.mem_coe] using
      (Classical.choose_spec ((blocks index).localized_function (value index)
      (hhomogeneous index) (hsupport index) (hnonzero index))).2 vertex
  change LinearIndependent ℂ (fun index =>
    (value index : DihedralGroup n → CoordinatePolynomial))
  rw [heq]
  exact hindependent

namespace Block
/-- Injectively distinct translates of a localized spline are independent. -/
theorem orbit_independent {I : Type*} [Fintype I] (block : Block ideal)
    (hbound : 2 * block.half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n,
      length n hthree alpha.reflection ≤ 2 * block.half + 1 → alpha.val ∈ ideal)
    (translate : I → DihedralGroup n)
    (hinjective : Function.Injective (fun index => (block.translate (translate index)).vertices))
    (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n)) block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    LinearIndependent ℂ (fun index => ideal.toRootSubset.dot hthree (translate index) value) := by
  apply ideal.block_splines_independent block.half hbound hselected
    (fun index => block.translate (translate index)) (fun _ => rfl) hinjective
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).1
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).2.1
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).2.2

/-- Distinct admissible translates remain independent for every proper odd ideal. -/
theorem odd_orbit_independent {I : Type*} [Fintype I] (block : Block ideal)
    (hcard : ideal.carrier.ncard = 2 * block.half + 1)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (translate : I → DihedralGroup n)
    (hinjective : Function.Injective (fun index => (block.translate (translate index)).vertices))
    (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n)) block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    LinearIndependent ℂ (fun index => ideal.toRootSubset.dot hthree (translate index) value) := by
  apply ideal.odd_block_splines_independent block.half hcard hproper
    (fun index => block.translate (translate index)) (fun _ => rfl) hinjective
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).1
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).2.1
  · exact fun index => (block.dot_localized (translate index) value hhomogeneous
      hsupport hnonzero).2.2
end Block

end Schubert.DihedralSplines.HessenbergIdeal
