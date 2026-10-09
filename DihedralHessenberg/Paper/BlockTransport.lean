import DihedralHessenberg.Dihedral.BlockTranslation
import DihedralHessenberg.Paper.BlockLocalization
import DihedralHessenberg.Paper.BoundaryTranslation

/-! # Dot transport of localized alternating blocks -/

noncomputable section

namespace Schubert.DihedralSplines.HessenbergIdeal.Block

open Schubert.Dihedral
open scoped Classical

variable {n : ℕ} {hthree : 3 ≤ n} {ideal : HessenbergIdeal n hthree}

/-- Left translation changes the base and preserves the selected terminal root. -/
def translate (block : Block ideal) (element : DihedralGroup n) : Block ideal :=
  { block with base := element * block.base }

/-- The translated vertices are the left image of the vertices. -/
theorem translate_vertices (block : Block ideal) (element : DihedralGroup n) :
    ((block.translate element).vertices : Set (DihedralGroup n)) =
      (fun vertex => element * vertex) '' (block.vertices : Set (DihedralGroup n)) := by
  rw [vertices, translate, alternatingBlock_translate]
  exact Finset.coe_image

/-- Translation preserves the outgoing-boundary degree at the translated base. -/
theorem translate_degree (block : Block ideal) (element : DihedralGroup n) :
    (ideal.toRootSubset.boundaryRoots
      ((block.translate element).vertices : Set (DihedralGroup n))
      (block.translate element).base).card =
    (ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n)) block.base).card :=
  by
  rw [translate_vertices]
  exact congrArg Finset.card
    (ideal.toRootSubset.boundaryRoots_translate _ element block.base)

variable [NeZero n]

/-- Dot transport preserves the block support and exact homogeneous boundary degree. -/
theorem dot_localized (block : Block ideal) (element : DihedralGroup n)
    (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card))
    (hsupport : ∀ vertex, vertex ∉ block.vertices →
      (value : DihedralGroup n → CoordinatePolynomial) vertex = 0)
    (hnonzero : value ≠ 0) :
    ideal.toRootSubset.dot hthree element value ∈ ideal.toRootSubset.piece
      ((ideal.toRootSubset.boundaryRoots
        ((block.translate element).vertices : Set (DihedralGroup n))
        (block.translate element).base).card) ∧
      (∀ vertex, vertex ∉ (block.translate element).vertices →
        (ideal.toRootSubset.dot hthree element value :
          DihedralGroup n → CoordinatePolynomial) vertex = 0) ∧
      ideal.toRootSubset.dot hthree element value ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [translate_degree]
    exact ideal.toRootSubset.dot_mem_piece hthree element _ value hhomogeneous
  · intro vertex hnot
    have houtside : element⁻¹ * vertex ∉ block.vertices := by
      intro hinside
      apply hnot
      change vertex ∈ ((block.translate element).vertices : Set (DihedralGroup n))
      rw [translate_vertices]
      exact ⟨element⁻¹ * vertex, hinside, mul_inv_cancel_left _ _⟩
    rw [ideal.toRootSubset.dot_apply, hsupport _ houtside, map_zero]
  · have hbase := block.base_ne_zero value hhomogeneous hsupport hnonzero
    have hdot := (ideal.toRootSubset.dot_support hthree element block.base value).mpr hbase
    intro hzero
    apply hdot
    rw [hzero]
    rfl

end Schubert.DihedralSplines.HessenbergIdeal.Block
