import Schubert.Dihedral.SimpleRootPermutation
import Mathlib.Data.Finset.Max

/-! # The sum of positive roots under simple reflections -/

noncomputable section

namespace Schubert.Dihedral

/-- The finite set of positive unit vectors. -/
def positiveFinset (n : ℕ) : Finset RealPlane :=
  (Set.finite_range (positiveRoot n)).toFinset

/-- The finite vector set has exactly the positive-root carrier. -/
@[simp] theorem mem_positiveFinset (n : ℕ) (vector : RealPlane) :
    vector ∈ positiveFinset n ↔ vector ∈ positiveRoots n := by
  classical
  simp only [positiveFinset, Set.Finite.mem_toFinset]
  rfl

/-- The sum of all positive unit roots. -/
def rootSum (n : ℕ) : RealPlane := ∑ vector ∈ positiveFinset n, vector

/-- A simple reflection changes the total root sum by twice its own normal. -/
theorem rootSum_reflection (n : ℕ) (hthree : 3 ≤ n) (simple : Fin 2) :
    realAction n (simpleRoot n hthree simple).reflection (rootSum n) =
      rootSum n - 2 • (simpleRoot n hthree simple).val := by
  classical
  let : NeZero n := ⟨by omega⟩
  let alpha := simpleRoot n hthree simple
  let others := (positiveFinset n).erase alpha.val
  have hmem (vector : RealPlane) : vector ∈ others ↔
      vector ∈ positiveRoots n \ {alpha.val} := by
    simp only [others, Finset.mem_erase, mem_positiveFinset, Set.mem_sdiff,
      Set.mem_singleton_iff]
    exact and_comm
  have hbij := simple_except_bijOn n hthree simple
  have hsum : ∑ vector ∈ others, realAction n alpha.reflection vector =
      ∑ vector ∈ others, vector := by
    apply Finset.sum_bij (fun vector _ => realAction n alpha.reflection vector)
    · intro vector hv
      exact (hmem _).mpr (hbij.mapsTo ((hmem _).mp hv))
    · intro first hfirst second hsecond heq
      exact hbij.injOn ((hmem _).mp hfirst) ((hmem _).mp hsecond) heq
    · intro vector hv
      obtain ⟨first, hf, heq⟩ := hbij.surjOn ((hmem _).mp hv)
      exact ⟨first, (hmem _).mpr hf, heq⟩
    · intro vector hv
      rfl
  have hroot : alpha.val ∈ positiveFinset n := (mem_positiveFinset _ _).mpr alpha.property
  have hsplit : rootSum n = (∑ vector ∈ others, vector) + alpha.val := by
    exact (Finset.sum_erase_add (positiveFinset n) id hroot).symm
  have hnormal : realAction n alpha.reflection alpha.val = -alpha.val := by
    have h := alpha.scaled_reflection 1 one_ne_zero alpha.val
    have hunit := roots_unit alpha.val (Or.inl alpha.property)
    simp only [one_smul, hunit, div_one, mul_one] at h
    rw [← h]
    funext coordinate
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  rw [hsplit]
  change (realLinearEquiv n alpha.reflection)
    ((∑ vector ∈ others, vector) + alpha.val) = _
  rw [map_add, map_sum]
  change (∑ vector ∈ others, realAction n alpha.reflection vector) +
    realAction n alpha.reflection alpha.val = _
  rw [hsum, hnormal]
  module

end Schubert.Dihedral
