import DihedralHessenberg.Dihedral.FirstBlockProper
import DihedralHessenberg.Dihedral.SecondBlockStabilizer
import DihedralHessenberg.Paper.BlockTransport

/-! # Terminal-reflection stabilizers of alternating blocks -/

namespace Schubert.DihedralSplines.HessenbergIdeal.Block

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n} {ideal : HessenbergIdeal n hthree}

private theorem baseline (block : Block ideal) (element : DihedralGroup n) :
    block.vertices.image (fun vertex => element * vertex) = block.vertices ↔
      (alternatingBlock 1 block.alpha block.beta block.half).image
          (fun vertex => (block.base⁻¹ * element * block.base) * vertex) =
        alternatingBlock 1 block.alpha block.beta block.half := by
  classical
  rw [vertices, ← alternatingBlock_translate, ← alternatingBlock_translate, mul_one]
  constructor
  · intro heq
    have himage := congrArg (fun vertices : Finset (DihedralGroup n) =>
      vertices.image (fun vertex => block.base⁻¹ * vertex)) heq
    simpa only [← alternatingBlock_translate, mul_assoc, inv_mul_cancel] using himage
  · intro heq
    have himage := congrArg (fun vertices : Finset (DihedralGroup n) =>
      vertices.image (fun vertex => block.base * vertex)) heq
    simpa only [← alternatingBlock_translate, ← mul_assoc, mul_inv_cancel, one_mul,
      mul_one] using himage

/-- A block is stabilized exactly by identity and its translated terminal reflection. -/
theorem stabilizer (block : Block ideal) (element : DihedralGroup n) :
    block.vertices.image (fun vertex => element * vertex) = block.vertices ↔
      element = 1 ∨ element = block.base * block.gamma.reflection * block.base⁻¹ := by
  classical
  rw [baseline]
  have hbound := block.bound
  have hterminal := block.terminal
  have hbase :
      (alternatingBlock 1 block.alpha block.beta block.half).image
          (fun vertex => (block.base⁻¹ * element * block.base) * vertex) =
        alternatingBlock 1 block.alpha block.beta block.half ↔
      block.base⁻¹ * element * block.base = 1 ∨
        block.base⁻¹ * element * block.base = block.gamma.reflection := by
    rcases block.pair with ⟨halpha, hbeta⟩ | ⟨halpha, hbeta⟩
    · rw [halpha, ite_eq_left rfl, Nat.add_zero] at hbound
      rw [halpha, hbeta, PositiveRoot.alternating_odd, simpleRoot_reflection,
        simpleRoot_reflection, simpleReflection_zero, simpleReflection_one] at hterminal
      have hreflection := numbered_even_reflection n block.half hbound
      have hgamma := hterminal.trans hreflection.symm
      rw [halpha, hbeta, first_block_stabilizer_proper block.half hbound, ← hgamma]
    · rw [halpha, ite_eq_right (simpleRoot_ne n hthree).symm] at hbound
      rw [halpha, hbeta, PositiveRoot.alternating_odd, simpleRoot_reflection,
        simpleRoot_reflection, simpleReflection_one, simpleReflection_zero] at hterminal
      have hreflection := numbered_odd_reflection n block.half hbound
      have hgamma := hterminal.trans hreflection.symm
      rw [halpha, hbeta, second_block_stabilizer block.half hbound, ← hgamma]
  rw [hbase]
  constructor
  · rintro (heq | heq)
    · left
      have heq := congrArg (fun current => block.base * current * block.base⁻¹) heq
      simp only [mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at heq
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using heq
    · right
      have heq := congrArg (fun current => block.base * current * block.base⁻¹) heq
      simp only [← mul_assoc, mul_inv_cancel, one_mul] at heq
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using heq
  · rintro (rfl | rfl)
    · left; group
    · right; group

/-- Equality of translated block vertices is the exact terminal-reflection condition. -/
theorem translate_stabilizer (block : Block ideal) (element : DihedralGroup n) :
    (block.translate element).vertices = block.vertices ↔
      element = 1 ∨ element = block.base * block.gamma.reflection * block.base⁻¹ := by
  rw [vertices, translate, alternatingBlock_translate]
  exact block.stabilizer element

/-- The left image of a block set has exactly its terminal-reflection stabilizer. -/
theorem image_stabilizer (block : Block ideal) (element : DihedralGroup n) :
    (fun vertex => element * vertex) '' (block.vertices : Set (DihedralGroup n)) =
        (block.vertices : Set (DihedralGroup n)) ↔
      element = 1 ∨ element = block.base * block.gamma.reflection * block.base⁻¹ := by
  classical
  rw [← Finset.coe_image, Finset.coe_inj]
  exact block.stabilizer element

end Schubert.DihedralSplines.HessenbergIdeal.Block
