import DihedralHessenberg.Paper.BoundaryPropagation
import DihedralHessenberg.Paper.HessenbergBlock

/-! # Nonzero localization on regular alternating blocks -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Block

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}

omit [NeZero n] in
/-- The boundary degree of a block equals its degree at the initial vertex. -/
theorem boundary_degree (block : Block ideal) (vertex : DihedralGroup n)
    (hvertex : vertex ∈ block.vertices) :
    (ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n)) vertex).card =
      (ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n)) block.base).card :=
  by
  rw [ideal.toRootSubset.boundaryRoots_card, ideal.toRootSubset.boundaryRoots_card]
  simpa only [Finset.mem_coe] using (block.boundary_card vertex hvertex).trans
    (block.boundary_card block.base
      (vertex_mem_alternatingBlock block.base block.alpha block.beta block.half)).symm

/-- A nonzero block-supported spline at boundary degree has nonzero initial value. -/
theorem base_ne_zero (block : Block ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    (value : DihedralGroup n → CoordinatePolynomial) block.base ≠ 0 := by
  have hsome : ∃ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
    by_contra hnone
    apply hnonzero
    apply Subtype.ext
    funext vertex
    change (value : DihedralGroup n → CoordinatePolynomial) vertex = 0
    by_contra hne
    exact hnone ⟨vertex, hne⟩
  obtain ⟨vertex, hvertex⟩ := hsome
  have hmem : vertex ∈ block.vertices := by
    by_contra hnot
    exact hvertex (hsupport vertex hnot)
  have heq := block.eq_of_edges (fun current =>
    (value : DihedralGroup n → CoordinatePolynomial) current ≠ 0) (by
      intro source hsource target htarget hedge
      exact propext (ideal.toRootSubset.nonzero_edge_iff
        (block.vertices : Set (DihedralGroup n)) value _ hhomogeneous hsupport
        (fun current hcurrent => block.boundary_degree current hcurrent)
        source target hsource htarget hedge)) vertex hmem
  exact Eq.mp heq hvertex

/-- Every supported nonzero boundary-degree spline has nonzero coefficients throughout the block. -/
theorem localized (block : Block ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) (vertex : DihedralGroup n) (hvertex : vertex ∈ block.vertices) :
    ∃ scalar : ℂ, scalar ≠ 0 ∧
      (value : DihedralGroup n → CoordinatePolynomial) vertex =
        MvPolynomial.C scalar * ideal.toRootSubset.boundaryProduct
          (block.vertices : Set (DihedralGroup n)) vertex := by
  have hbase := block.base_ne_zero value hhomogeneous hsupport hnonzero
  have hnonzeroVertex := ideal.toRootSubset.nonzero_on
    (block.vertices : Set (DihedralGroup n)) value _ hhomogeneous hsupport
    (fun current hcurrent => block.boundary_degree current hcurrent) block.base
    (fun invariant hinvariant => block.eq_of_edges invariant
      (fun source hs target ht hedge => hinvariant source target hs ht hedge)) hbase vertex hvertex
  obtain ⟨scalar, hscalar⟩ := ideal.toRootSubset.localized
    (block.vertices : Set (DihedralGroup n)) value _ hhomogeneous hsupport vertex
    (block.boundary_degree vertex hvertex)
  refine ⟨scalar, ?_, hscalar⟩
  intro hzero
  apply hnonzeroVertex
  simp [hscalar, hzero]

/-- The pointwise localization witnesses assemble into the displayed coefficient function. -/
theorem localized_function (block : Block ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    ∃ coefficient : DihedralGroup n → ℂ,
      (∀ vertex ∈ block.vertices, coefficient vertex ≠ 0) ∧
      ∀ vertex, (value : DihedralGroup n → CoordinatePolynomial) vertex =
        if vertex ∈ block.vertices then MvPolynomial.C (coefficient vertex) *
          ideal.toRootSubset.boundaryProduct (block.vertices : Set (DihedralGroup n)) vertex
        else 0 := by
  classical
  let coefficient : DihedralGroup n → ℂ := fun vertex =>
    if hvertex : vertex ∈ block.vertices then
      Classical.choose (block.localized value hhomogeneous hsupport hnonzero vertex hvertex)
    else 0
  refine ⟨coefficient, ?_, ?_⟩
  · intro vertex hvertex
    dsimp only [coefficient]
    rw [dite_eq_left hvertex]
    exact (Classical.choose_spec
      (block.localized value hhomogeneous hsupport hnonzero vertex hvertex)).1
  · intro vertex
    by_cases hvertex : vertex ∈ block.vertices
    · rw [ite_eq_left hvertex]
      dsimp only [coefficient]
      rw [dite_eq_left hvertex]
      exact (Classical.choose_spec
        (block.localized value hhomogeneous hsupport hnonzero vertex hvertex)).2
    · rw [ite_eq_right hvertex]
      exact hsupport vertex hvertex

/-- A nonzero block spline gives a unique normalization with initial coefficient one. -/
theorem normalized_unique (block : Block ideal) (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    ∃! normalized : ideal.toRootSubset.Spline,
      normalized ∈ ideal.toRootSubset.piece
        ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
          block.base).card) ∧
      (∀ vertex, vertex ∉ block.vertices →
        (normalized : DihedralGroup n → CoordinatePolynomial) vertex = 0) ∧
      (normalized : DihedralGroup n → CoordinatePolynomial) block.base =
        ideal.toRootSubset.boundaryProduct (block.vertices : Set (DihedralGroup n))
          block.base := by
  have hbaseMem := vertex_mem_alternatingBlock block.base block.alpha block.beta block.half
  obtain ⟨scalar, hscalar, hvalue⟩ := block.localized value hhomogeneous hsupport hnonzero
    block.base hbaseMem
  let normalized := scalar⁻¹ • value
  have hnormalPiece : normalized ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card) :=
    (ideal.toRootSubset.piece _).smul_mem scalar⁻¹ hhomogeneous
  have hnormalSupport : ∀ vertex, vertex ∉ block.vertices →
      (normalized : DihedralGroup n → CoordinatePolynomial) vertex = 0 := by
    intro vertex hnot
    change scalar⁻¹ • (value : DihedralGroup n → CoordinatePolynomial) vertex = 0
    rw [hsupport vertex hnot, smul_zero]
  have hnormalBase : (normalized : DihedralGroup n → CoordinatePolynomial) block.base =
      ideal.toRootSubset.boundaryProduct (block.vertices : Set (DihedralGroup n))
        block.base := by
    change scalar⁻¹ • (value : DihedralGroup n → CoordinatePolynomial) block.base = _
    rw [hvalue, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul,
      inv_mul_cancel₀ hscalar, map_one, one_mul]
  refine ⟨normalized, ⟨hnormalPiece, hnormalSupport, hnormalBase⟩, ?_⟩
  intro other hother
  apply sub_eq_zero.mp
  apply ideal.toRootSubset.eq_zero_of_base (block.vertices : Set (DihedralGroup n))
    (other - normalized) _ ((ideal.toRootSubset.piece _).sub_mem hother.1 hnormalPiece)
    (fun vertex hnot => by
      change (other : DihedralGroup n → CoordinatePolynomial) vertex -
        (normalized : DihedralGroup n → CoordinatePolynomial) vertex = 0
      rw [hother.2.1 vertex hnot, hnormalSupport vertex hnot, sub_self])
    (fun current hcurrent => block.boundary_degree current hcurrent) block.base
    (fun invariant hinvariant => block.eq_of_edges invariant
      (fun source hs target ht hedge => hinvariant source target hs ht hedge))
  change (other : DihedralGroup n → CoordinatePolynomial) block.base -
    (normalized : DihedralGroup n → CoordinatePolynomial) block.base = 0
  rw [hother.2.2, hnormalBase, sub_self]

end Schubert.DihedralSplines.HessenbergIdeal.Block
