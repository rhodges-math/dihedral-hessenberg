import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Lifting scalar-ideal basis combinations through algebra maps -/

noncomputable section
namespace Schubert.Splines
variable {R A B I : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Fintype I]

/-- Scalar-ideal coordinates lift when every active basis vector has a preimage. -/
theorem ideal_basis_preimage (scalarIdeal : Ideal R) (map : A →ₐ[R] B)
    (basis : Module.Basis I R B) (value : B)
    (hcoords : ∀ index, basis.repr value index ∈ scalarIdeal)
    (hlift : ∀ index, basis.repr value index ≠ 0 → ∃ original, map original = basis index) :
    ∃ original ∈ Ideal.map (algebraMap R A) scalarIdeal, map original = value := by
  classical
  let lift : I → A := fun index =>
    if h : basis.repr value index ≠ 0 then Classical.choose (hlift index h) else 0
  refine ⟨∑ index, basis.repr value index • lift index, ?_, ?_⟩
  · apply Submodule.sum_mem
    intro index _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hcoords index))
  · rw [map_sum]
    have hterm : ∀ index, map (basis.repr value index • lift index) =
        basis.repr value index • basis index := by
      intro index
      rw [map_smul]
      by_cases h : basis.repr value index ≠ 0
      · dsimp only [lift]
        rw [dite_eq_left h, Classical.choose_spec (hlift index h)]
      · simp [not_not.mp h]
    simp_rw [hterm]
    exact basis.sum_repr value
end Schubert.Splines
