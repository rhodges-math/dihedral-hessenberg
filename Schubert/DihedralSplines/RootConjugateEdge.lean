import Schubert.DihedralSplines.PaperGraph
import Schubert.DihedralSplines.HessenbergReflectionLength
import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.Dihedral.RootSubsetCard

/-! # Selected conjugate reflections and endpoint edges -/

namespace Schubert.Dihedral.RootSubset

/-- Reversing an endpoint edge preserves its selected root. -/
theorem edge_symm {n : ℕ} (selected : RootSubset n) {source target : DihedralGroup n}
    (hedge : (source, target) ∈ selected.edges) : (target, source) ∈ selected.edges := by
  obtain ⟨alpha, hselected, hneighbor⟩ := (selected.mem_edges _).mp hedge
  apply (selected.mem_edges _).mpr
  refine ⟨alpha, hselected, ?_⟩
  change source = target * alpha.reflection
  change target = source * alpha.reflection at hneighbor
  rw [hneighbor, mul_assoc, PositiveRoot.reflection_square, mul_one]

/-- The outgoing endpoint neighbors are counted by selected positive vectors. -/
theorem neighbor_card {n : ℕ} (selected : RootSubset n) (source : DihedralGroup n) :
    {target : DihedralGroup n | (source, target) ∈ selected.edges}.ncard =
      selected.carrier.ncard := by
  have hset : {target : DihedralGroup n | (source, target) ∈ selected.edges} =
      (fun index : PositiveRootIndex n => source * rootReflection index) '' selected.indices := by
    ext target
    simp only [Set.mem_ofPred_eq, selected.mem_edges_iff_index, Set.mem_image]
    constructor
    · rintro ⟨index, hselected, htarget⟩
      exact ⟨index, hselected, htarget.symm⟩
    · rintro ⟨index, hselected, htarget⟩
      exact ⟨index, hselected, htarget.symm⟩
  have hinjective : Function.Injective (fun index : PositiveRootIndex n =>
      source * rootReflection index) := fun _ _ h => rootReflection_injective n (mul_left_cancel h)
  rw [hset, Set.ncard_image_of_injective _ hinjective, selected.ncard_indices]
  exact Set.ncard_eq_toFinset_card selected.indices

/-- Descending endpoint neighbors are counted by the root-valued inversion statistic. -/
theorem descending_card {n : ℕ} (hthree : 3 ≤ n) (selected : RootSubset n)
    (source : DihedralGroup n) :
    {target : DihedralGroup n | (source, target) ∈ selected.edges ∧
      Schubert.Dihedral.length n hthree target < Schubert.Dihedral.length n hthree source}.ncard =
        selected.length source := by
  classical
  let indices := selected.indicesFinset ∩ rightInversions n hthree source
  have hset : {target : DihedralGroup n | (source, target) ∈ selected.edges ∧
      Schubert.Dihedral.length n hthree target < Schubert.Dihedral.length n hthree source} =
      (indices.image (fun index => source * rootReflection index) : Set (DihedralGroup n)) := by
    ext target
    simp only [Set.mem_ofPred_eq, selected.mem_edges_iff_index, Finset.mem_coe,
      Finset.mem_image, indices, Finset.mem_inter, selected.mem_indicesFinset,
      selected.mem_indices, mem_rightInversions]
    constructor
    · rintro ⟨⟨index, hselected, rfl⟩, hdescend⟩
      exact ⟨index, ⟨hselected, hdescend⟩, rfl⟩
    · rintro ⟨index, ⟨hselected, hdescend⟩, rfl⟩
      exact ⟨⟨index, hselected, rfl⟩, hdescend⟩
  have hinjective : Function.Injective (fun index : PositiveRootIndex n =>
      source * rootReflection index) := fun _ _ h => rootReflection_injective n (mul_left_cancel h)
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinjective,
    selected.length_indices hthree]

/-- A conjugated root reflection determines the selected root of a left endpoint edge. -/
theorem edge_iff_conjugate {n : ℕ} (selected : RootSubset n)
    (alpha gamma : PositiveRoot n) (element : DihedralGroup n)
    (hconjugate : gamma.reflection = element⁻¹ * alpha.reflection * element) :
    (element, alpha.reflection * element) ∈ selected.edges ↔ gamma.val ∈ selected := by
  have hneighbor : alpha.reflection * element = element * gamma.reflection := by
    rw [hconjugate]
    group
  rw [selected.mem_edges]
  constructor
  · rintro ⟨beta, hselected, htarget⟩
    change alpha.reflection * element = element * beta.reflection at htarget
    have heq : beta = gamma := PositiveRoot.reflection_injective n
      (mul_left_cancel (htarget.symm.trans hneighbor))
    simpa only [heq] using hselected
  · exact fun hselected => ⟨gamma, hselected, hneighbor⟩

end Schubert.Dihedral.RootSubset

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A selected vector has reflection length bounded by the cardinality of its ideal. -/
theorem reflection_length_le (ideal : HessenbergIdeal n hthree) (gamma : PositiveRoot n)
    (hselected : gamma.val ∈ ideal) :
    Schubert.Dihedral.length n hthree gamma.reflection ≤ ideal.carrier.ncard := by
  rw [ideal.ncard_indexed]
  apply ideal.indexed.reflection_length_le_card_of_mem gamma.index
  rw [ideal.mem_indexed, PositiveRoot.index_val]
  exact hselected

/-- A vector with strictly smaller reflection length than the ideal size is selected. -/
theorem selected_of_short (ideal : HessenbergIdeal n hthree) (gamma : PositiveRoot n)
    (hshort : Schubert.Dihedral.length n hthree gamma.reflection < ideal.carrier.ncard) :
    gamma.val ∈ ideal := by
  rw [ideal.ncard_indexed] at hshort
  have hselected := ideal.indexed.mem_roots_of_reflection_length_lt_card gamma.index hshort
  simpa only [ideal.mem_indexed, PositiveRoot.index_val] using hselected

end Schubert.DihedralSplines.HessenbergIdeal
