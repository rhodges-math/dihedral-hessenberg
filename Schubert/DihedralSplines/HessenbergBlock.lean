import Schubert.Dihedral.RootBlock
import Schubert.Dihedral.RootNumbering
import Schubert.DihedralSplines.AlternatingBlockRegular
import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.DihedralSplines.PaperGraph

/-! # Regular alternating blocks in Hessenberg graphs -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem prefix_product (simple : Fin 2) (size : ℕ) :
    (simpleRoot n hthree simple).alternatingProduct
      (simpleRoot n hthree simple.rev) size =
        alternatingPrefixProduct n hthree simple size := by
  simpa only [Fin.rev_rev, alternatingPrefixProduct] using
    PositiveRoot.alternatingProduct_indexed n hthree simple.rev size

private theorem simple_bound (simple : Fin 2) (half : ℕ)
    (hbound : 2 * half + (if simpleRoot n hthree simple = simpleRoot n hthree 0
      then 0 else 1) < n) : 2 * half + simple.val < n := by
  fin_cases simple
  · change 2 * half + 0 < n
    change 2 * half + (if simpleRoot n hthree 0 = simpleRoot n hthree 0 then 0 else 1) < n
      at hbound
    rw [ite_eq_left rfl] at hbound
    exact hbound
  · change 2 * half + 1 < n
    change 2 * half + (if simpleRoot n hthree 1 = simpleRoot n hthree 0 then 0 else 1) < n
      at hbound
    simpa only [ite_eq_right (simpleRoot_ne n hthree).symm] using hbound

private theorem endpoint_reflection (simple : Fin 2) (half : ℕ)
    (hbound : 2 * half + simple.val < n) :
    (positiveRootEquiv n ⟨2 * half + simple.val, hbound⟩).reflection =
      (simpleRoot n hthree simple).alternatingProduct
        (simpleRoot n hthree simple.rev) (2 * half + 1) := by
  rw [PositiveRoot.alternating_odd, simpleRoot_reflection, simpleRoot_reflection]
  fin_cases simple
  · change (positiveRootEquiv n ⟨2 * half + 0, hbound⟩).reflection =
      (simpleReflection n 0 * simpleReflection n 1) ^ half * simpleReflection n 0
    rw [simpleReflection_zero, simpleReflection_one]
    simpa only [Nat.add_zero] using numbered_even_reflection n half (by omega)
  · change (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection =
      (simpleReflection n 1 * simpleReflection n 0) ^ half * simpleReflection n 1
    rw [simpleReflection_one, simpleReflection_zero]
    exact numbered_odd_reflection n half hbound

/-- A bounded alternating block has exactly its specified number of prefix vertices. -/
private theorem block_card (vertex : DihedralGroup n) (alpha beta : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n) :
    (alternatingBlock vertex alpha beta half).card = 2 * half + 2 := by
  obtain ⟨simple, rfl, rfl⟩ := simple_pair_index alpha beta hpair
  have hindex := simple_bound simple half hbound
  let endpoint : PositiveRootIndex n := ⟨2 * half + simple.val, hindex⟩
  unfold alternatingBlock
  simp_rw [prefix_product]
  exact HessenbergSpace.card_alternating_block simple half endpoint rfl vertex

/-- A selected terminal reflection makes the induced block graph complete bipartite. -/
private theorem block_edge (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n)
    (hgamma : gamma.val ∈ ideal)
    (hreflection : gamma.reflection = alpha.alternatingProduct beta (2 * half + 1))
    (first second : ℕ) (hfirst : first < 2 * half + 2) (hsecond : second < 2 * half + 2) :
    (vertex * alpha.alternatingProduct beta first,
      vertex * alpha.alternatingProduct beta second) ∈ ideal.toRootSubset.edges ↔
        first % 2 ≠ second % 2 := by
  obtain ⟨simple, rfl, rfl⟩ := simple_pair_index alpha beta hpair
  have hindex := simple_bound simple half hbound
  let endpoint : PositiveRootIndex n := ⟨2 * half + simple.val, hindex⟩
  have heq : positiveRootEquiv n endpoint = gamma := by
    apply PositiveRoot.reflection_injective n
    exact (endpoint_reflection simple half hindex).trans hreflection.symm
  have hmem : endpoint ∈ ideal.indexed.roots := by
    rw [ideal.mem_indexed]
    simpa only [← positiveRootEquiv_val n endpoint, heq] using hgamma
  rw [RootSubset.mem_edges_iff_index, ← ideal.indexed_roots]
  simp only [Finset.mem_coe]
  simp_rw [prefix_product]
  exact ideal.indexed.alternating_block_edge_iff_parity_ne simple half endpoint rfl hmem
    vertex first second (by omega) (by omega)

/-- Functions invariant on internal block edges are constant throughout the block. -/
private theorem eq_on_block (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n)
    (hgamma : gamma.val ∈ ideal)
    (hreflection : gamma.reflection = alpha.alternatingProduct beta (2 * half + 1))
    {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source ∈ alternatingBlock vertex alpha beta half,
      ∀ target ∈ alternatingBlock vertex alpha beta half,
        (source, target) ∈ ideal.toRootSubset.edges → value source = value target) :
    ∀ target ∈ alternatingBlock vertex alpha beta half, value target = value vertex := by
  intro target htarget
  obtain ⟨position, hposition, rfl⟩ :=
    (mem_alternatingBlock vertex target alpha beta half).mp htarget
  have hzero := vertex_mem_alternatingBlock vertex alpha beta half
  have hpositionMem := (mem_alternatingBlock vertex _ alpha beta half).mpr
    ⟨position, hposition, rfl⟩
  have hfirstMem := (mem_alternatingBlock vertex _ alpha beta half).mpr
    ⟨1, by omega, rfl⟩
  by_cases hodd : position % 2 ≠ 0
  · apply hinvariant _ hpositionMem vertex hzero
    have hedge := (ideal.block_edge vertex alpha beta gamma hpair half hbound hgamma
      hreflection position 0 hposition (by omega)).mpr (by simpa only [Nat.zero_mod] using hodd)
    simpa only [PositiveRoot.alternating_zero, mul_one] using hedge
  · apply (hinvariant _ hpositionMem _ hfirstMem ?_).trans
      (hinvariant _ hfirstMem vertex hzero ?_)
    · apply (ideal.block_edge vertex alpha beta gamma hpair half hbound hgamma
        hreflection position 1 hposition (by omega)).mpr
      omega
    · have hedge := (ideal.block_edge vertex alpha beta gamma hpair half hbound hgamma
        hreflection 1 0 (by omega) (by omega)).mpr (by decide)
      simpa only [PositiveRoot.alternating_zero, mul_one] using hedge

/-- Every vertex in a selected alternating block has the same internal degree. -/
private theorem block_internal_card (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n)
    (hgamma : gamma.val ∈ ideal)
    (hreflection : gamma.reflection = alpha.alternatingProduct beta (2 * half + 1))
    (position : ℕ) (hposition : position < 2 * half + 2) :
    {target : DihedralGroup n |
      (vertex * alpha.alternatingProduct beta position, target) ∈ ideal.toRootSubset.edges ∧
        target ∈ alternatingBlock vertex alpha beta half}.ncard = half + 1 := by
  classical
  obtain ⟨simple, rfl, rfl⟩ := simple_pair_index alpha beta hpair
  have hindex := simple_bound simple half hbound
  let endpoint : PositiveRootIndex n := ⟨2 * half + simple.val, hindex⟩
  have heq : positiveRootEquiv n endpoint = gamma := by
    apply PositiveRoot.reflection_injective n
    exact (endpoint_reflection simple half hindex).trans hreflection.symm
  have hmem : endpoint ∈ ideal.indexed.roots := by
    rw [ideal.mem_indexed]
    simpa only [← positiveRootEquiv_val n endpoint, heq] using hgamma
  unfold alternatingBlock
  simp_rw [prefix_product]
  let source := vertex * alternatingPrefixProduct n hthree simple position
  let block := (Finset.range (2 * half + 2)).image
    (fun second => vertex * alternatingPrefixProduct n hthree simple second)
  let indices := ideal.indexed.roots.filter (fun index => source * rootReflection index ∈ block)
  change {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
    target ∈ block}.ncard = half + 1
  have hset : {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∈ block} =
        (indices.image (fun index => source * rootReflection index) : Set (DihedralGroup n)) := by
    ext target
    simp only [Set.mem_ofPred_eq, RootSubset.mem_edges_iff_index, ← ideal.indexed_roots,
      Finset.mem_coe, Finset.mem_image, indices, Finset.mem_filter]
    constructor
    · rintro ⟨⟨index, hroot, htarget⟩, hblock⟩
      exact ⟨index, ⟨hroot, htarget ▸ hblock⟩, htarget.symm⟩
    · rintro ⟨index, ⟨hroot, hblock⟩, rfl⟩
      exact ⟨⟨index, hroot, rfl⟩, hblock⟩
  have hinjective : Function.Injective (fun index : PositiveRootIndex n =>
      source * rootReflection index) := fun _ _ h => rootReflection_injective n (mul_left_cancel h)
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinjective]
  exact ideal.indexed.card_internal_roots_alternating_block simple half endpoint rfl hmem
    vertex position hposition

/-- Every vertex in a selected alternating block has the same outgoing boundary degree. -/
private theorem block_boundary_card (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (alpha beta gamma : PositiveRoot n)
    (hpair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0))
    (half : ℕ) (hbound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n)
    (hgamma : gamma.val ∈ ideal)
    (hreflection : gamma.reflection = alpha.alternatingProduct beta (2 * half + 1))
    (position : ℕ) (hposition : position < 2 * half + 2) :
    {target : DihedralGroup n |
      (vertex * alpha.alternatingProduct beta position, target) ∈ ideal.toRootSubset.edges ∧
        target ∉ alternatingBlock vertex alpha beta half}.ncard =
          ideal.carrier.ncard - (half + 1) := by
  classical
  obtain ⟨simple, rfl, rfl⟩ := simple_pair_index alpha beta hpair
  have hindex := simple_bound simple half hbound
  let endpoint : PositiveRootIndex n := ⟨2 * half + simple.val, hindex⟩
  have heq : positiveRootEquiv n endpoint = gamma := by
    apply PositiveRoot.reflection_injective n
    exact (endpoint_reflection simple half hindex).trans hreflection.symm
  have hmem : endpoint ∈ ideal.indexed.roots := by
    rw [ideal.mem_indexed]
    simpa only [← positiveRootEquiv_val n endpoint, heq] using hgamma
  unfold alternatingBlock
  simp_rw [prefix_product]
  let source := vertex * alternatingPrefixProduct n hthree simple position
  let block := (Finset.range (2 * half + 2)).image
    (fun second => vertex * alternatingPrefixProduct n hthree simple second)
  let indices := ideal.indexed.roots.filter (fun index => source * rootReflection index ∉ block)
  change {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
    target ∉ block}.ncard = ideal.carrier.ncard - (half + 1)
  have hset : {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∉ block} =
        (indices.image (fun index => source * rootReflection index) : Set (DihedralGroup n)) := by
    ext target
    simp only [Set.mem_ofPred_eq, RootSubset.mem_edges_iff_index, ← ideal.indexed_roots,
      Finset.mem_coe, Finset.mem_image, indices, Finset.mem_filter]
    constructor
    · rintro ⟨⟨index, hroot, htarget⟩, hblock⟩
      exact ⟨index, ⟨hroot, htarget ▸ hblock⟩, htarget.symm⟩
    · rintro ⟨index, ⟨hroot, hblock⟩, rfl⟩
      exact ⟨⟨index, hroot, rfl⟩, hblock⟩
  have hinjective : Function.Injective (fun index : PositiveRootIndex n =>
      source * rootReflection index) := fun _ _ h => rootReflection_injective n (mul_left_cancel h)
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ hinjective,
    ideal.ncard_indexed]
  exact ideal.indexed.card_boundary_roots_alternating_block simple half endpoint rfl hmem
    vertex position hposition

/-- A bounded alternating block with a selected terminal reflection. -/
structure Block (ideal : HessenbergIdeal n hthree) where
  /-- The initial vertex. -/
  base : DihedralGroup n
  /-- The first simple root. -/
  alpha : PositiveRoot n
  /-- The second simple root. -/
  beta : PositiveRoot n
  /-- The terminal positive root. -/
  gamma : PositiveRoot n
  /-- Half the number of steps preceding the terminal reflection. -/
  half : ℕ
  /-- The two possible orders of the simple roots. -/
  pair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
    (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)
  /-- The terminal root belongs to the alternating enumeration. -/
  bound : 2 * half + (if alpha = simpleRoot n hthree 0 then 0 else 1) < n
  /-- The terminal root belongs to the ideal. -/
  selected : gamma.val ∈ ideal
  /-- The terminal reflection is the odd alternating product. -/
  terminal : gamma.reflection = alpha.alternatingProduct beta (2 * half + 1)

namespace Block

variable {ideal : HessenbergIdeal n hthree}

/-- The finite set of alternating prefix vertices. -/
noncomputable def vertices (block : Block ideal) : Finset (DihedralGroup n) :=
  alternatingBlock block.base block.alpha block.beta block.half

/-- The cardinality of the prefix set. -/
theorem card (block : Block ideal) : block.vertices.card = 2 * block.half + 2 :=
  block_card block.base block.alpha block.beta block.pair block.half block.bound

/-- Internal edges connect exactly the prefixes of opposite parity. -/
theorem edge (block : Block ideal) (first second : ℕ)
    (hfirst : first < 2 * block.half + 2) (hsecond : second < 2 * block.half + 2) :
    (block.base * block.alpha.alternatingProduct block.beta first,
      block.base * block.alpha.alternatingProduct block.beta second) ∈ ideal.toRootSubset.edges ↔
        first % 2 ≠ second % 2 :=
  ideal.block_edge block.base block.alpha block.beta block.gamma block.pair block.half
    block.bound block.selected block.terminal first second hfirst hsecond

/-- Edge-invariant functions are constant on the block. -/
theorem eq_of_edges (block : Block ideal) {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source ∈ block.vertices, ∀ target ∈ block.vertices,
      (source, target) ∈ ideal.toRootSubset.edges → value source = value target) :
    ∀ target ∈ block.vertices, value target = value block.base :=
  ideal.eq_on_block block.base block.alpha block.beta block.gamma block.pair block.half
    block.bound block.selected block.terminal value hinvariant

/-- Every block vertex has the same internal degree. -/
theorem internal_card (block : Block ideal) (source : DihedralGroup n)
    (hsource : source ∈ block.vertices) :
    {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∈ block.vertices}.ncard = block.half + 1 := by
  obtain ⟨position, hposition, rfl⟩ :=
    (mem_alternatingBlock block.base source block.alpha block.beta block.half).mp hsource
  exact ideal.block_internal_card block.base block.alpha block.beta block.gamma block.pair
    block.half block.bound block.selected block.terminal position hposition

/-- Every block vertex has the same outgoing boundary degree. -/
theorem boundary_card (block : Block ideal) (source : DihedralGroup n)
    (hsource : source ∈ block.vertices) :
    {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∉ block.vertices}.ncard = ideal.carrier.ncard - (block.half + 1) := by
  obtain ⟨position, hposition, rfl⟩ :=
    (mem_alternatingBlock block.base source block.alpha block.beta block.half).mp hsource
  exact ideal.block_boundary_card block.base block.alpha block.beta block.gamma block.pair
    block.half block.bound block.selected block.terminal position hposition

/-- The block starting with the first simple root. -/
noncomputable def first (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (half : ℕ) (hbound : 2 * half < n)
    (hselected : (positiveRootEquiv n ⟨2 * half, hbound⟩).val ∈ ideal) : Block ideal where
  base := vertex
  alpha := simpleRoot n hthree 0
  beta := simpleRoot n hthree 1
  gamma := positiveRootEquiv n ⟨2 * half, hbound⟩
  half := half
  pair := Or.inl ⟨rfl, rfl⟩
  bound := by
    rw [ite_eq_left rfl, Nat.add_zero]
    exact hbound
  selected := hselected
  terminal := by
    simpa using endpoint_reflection (n := n) (hthree := hthree) 0 half (by simpa using hbound)

/-- The block starting with the second simple root. -/
noncomputable def second (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).val ∈ ideal) : Block ideal where
  base := vertex
  alpha := simpleRoot n hthree 1
  beta := simpleRoot n hthree 0
  gamma := positiveRootEquiv n ⟨2 * half + 1, hbound⟩
  half := half
  pair := Or.inr ⟨rfl, rfl⟩
  bound := by simpa only [ite_eq_right (simpleRoot_ne n hthree).symm] using hbound
  selected := hselected
  terminal := by
    simpa using endpoint_reflection (n := n) (hthree := hthree) 1 half (by simpa using hbound)

end Block

/-- The alternating block starting with the first simple root is regular. -/
theorem first_regular (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (half : ℕ) (hbound : 2 * half < n)
    (hselected : (positiveRootEquiv n ⟨2 * half, hbound⟩).val ∈ ideal)
    (source : DihedralGroup n)
    (hsource : source ∈ alternatingBlock vertex (simpleRoot n hthree 0)
      (simpleRoot n hthree 1) half) :
    {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∈ alternatingBlock vertex (simpleRoot n hthree 0)
        (simpleRoot n hthree 1) half}.ncard = half + 1 :=
  (Block.first ideal vertex half hbound hselected).internal_card source hsource

/-- The alternating block starting with the second simple root is regular. -/
theorem second_regular (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).val ∈ ideal)
    (source : DihedralGroup n)
    (hsource : source ∈ alternatingBlock vertex (simpleRoot n hthree 1)
      (simpleRoot n hthree 0) half) :
    {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      target ∈ alternatingBlock vertex (simpleRoot n hthree 1)
        (simpleRoot n hthree 0) half}.ncard = half + 1 :=
  (Block.second ideal vertex half hbound hselected).internal_card source hsource

end Schubert.DihedralSplines.HessenbergIdeal
