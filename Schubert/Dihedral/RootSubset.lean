import Schubert.Dihedral.RootObjects
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Card

/-! # Subsets of the positive root vectors -/

noncomputable section

namespace Schubert.Dihedral

/-- A subset of the positive unit root vectors. -/
structure RootSubset (n : ℕ) where
  /-- The selected real root vectors. -/
  carrier : Set RealPlane
  /-- Every selected vector is a positive root. -/
  positive : carrier ⊆ positiveRoots n

instance (n : ℕ) : SetLike (RootSubset n) RealPlane where
  coe := RootSubset.carrier
  coe_injective := by
    intro first second heq
    cases first
    cases second
    cases heq
    rfl

namespace RootSubset

/-- Subsets with the same selected vectors agree. -/
@[ext] theorem ext {n : ℕ} {first second : RootSubset n}
    (hmembers : ∀ alpha, alpha ∈ first ↔ alpha ∈ second) : first = second :=
  SetLike.ext hmembers

/-- The finite index subset corresponding to a selected vector subset. -/
def indices {n : ℕ} (selected : RootSubset n) : Set (PositiveRootIndex n) :=
  {index | positiveRoot n index ∈ selected}

/-- A selected root is a positive root vector. -/
def root {n : ℕ} (selected : RootSubset n) (alpha : RealPlane) (hmem : alpha ∈ selected) :
    PositiveRoot n := ⟨alpha, selected.positive hmem⟩

/-- Index membership is exactly membership of the corresponding vector. -/
@[simp] theorem mem_indices {n : ℕ} (selected : RootSubset n) (index : PositiveRootIndex n) :
    index ∈ selected.indices ↔ positiveRoot n index ∈ selected := Iff.rfl

/-- Every vector subset is recovered as the image of its finite index subset. -/
theorem image_indices {n : ℕ} (selected : RootSubset n) :
    positiveRoot n '' selected.indices = selected.carrier := by
  ext alpha
  constructor
  · rintro ⟨index, hindex, rfl⟩
    exact hindex
  · intro hmem
    obtain ⟨index, hindex⟩ := selected.positive hmem
    refine ⟨index, ?_, hindex⟩
    change positiveRoot n index ∈ selected
    rw [hindex]
    exact hmem

/-- A selected positive-root subset is finite. -/
theorem finite {n : ℕ} (selected : RootSubset n) : selected.carrier.Finite :=
  (Set.finite_range (positiveRoot n)).subset selected.positive

/-- Numbering restricts to a bijection between selected indices and selected vectors. -/
def indexEquiv {n : ℕ} (selected : RootSubset n) :
    {index : PositiveRootIndex n // index ∈ selected.indices} ≃
      {alpha : RealPlane // alpha ∈ selected} :=
  Equiv.ofBijective (fun index => ⟨positiveRoot n index.val, index.property⟩) (by
    constructor
    · intro first second heq
      exact Subtype.ext (positiveRoot_injective n (congrArg Subtype.val heq))
    · intro alpha
      obtain ⟨index, hindex⟩ := selected.positive alpha.property
      refine ⟨⟨index, ?_⟩, Subtype.ext hindex⟩
      change positiveRoot n index ∈ selected
      rw [hindex]
      exact alpha.property)

/-- The selected indices as a finite set. -/
def indicesFinset {n : ℕ} (selected : RootSubset n) : Finset (PositiveRootIndex n) :=
  selected.indices.toFinite.toFinset

/-- Finite-index membership agrees with the selected vector. -/
@[simp] theorem mem_indicesFinset {n : ℕ} (selected : RootSubset n)
    (index : PositiveRootIndex n) :
    index ∈ selected.indicesFinset ↔ positiveRoot n index ∈ selected := by
  simp only [indicesFinset, Set.Finite.mem_toFinset, mem_indices]

/-- Any selected index set determines its positive-vector subset. -/
def ofIndices {n : ℕ} (selected : Set (PositiveRootIndex n)) : RootSubset n where
  carrier := positiveRoot n '' selected
  positive := by rintro _ ⟨index, _, rfl⟩; exact ⟨index, rfl⟩

/-- Selecting vectors and recovering indices are inverse operations. -/
@[simp] theorem indices_ofIndices {n : ℕ} (selected : Set (PositiveRootIndex n)) :
    (ofIndices selected).indices = selected := by
  ext index
  change positiveRoot n index ∈ positiveRoot n '' selected ↔ index ∈ selected
  rw [Set.mem_image]
  constructor
  · rintro ⟨other, hother, heq⟩
    exact (positiveRoot_injective n heq) ▸ hother
  · intro hmem
    exact ⟨index, hmem, rfl⟩

/-- Recovering indices and selecting their vectors returns the subset. -/
@[simp] theorem ofIndices_indices {n : ℕ} (selected : RootSubset n) :
    ofIndices selected.indices = selected := by
  apply SetLike.coe_injective
  exact selected.image_indices

end RootSubset

end Schubert.Dihedral
