import Schubert.Dihedral.RootSubset
import Schubert.DihedralSplines.RootOrder

/-! # Hessenberg ideals as subsets of positive root vectors -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- A lower subset of positive vectors containing both simple roots. -/
structure HessenbergIdeal (n : ℕ) (hthree : 3 ≤ n) extends RootSubset n where
  /-- Every positive root below a selected root is selected. -/
  lower : ∀ ⦃alpha beta : PositiveRoot n⦄,
    RootOrder n hthree alpha beta → beta.val ∈ carrier → alpha.val ∈ carrier
  /-- The first simple vector is selected. -/
  first_mem : (simpleRoot n hthree 0).val ∈ carrier
  /-- The second simple vector is selected. -/
  second_mem : (simpleRoot n hthree 1).val ∈ carrier

instance (n : ℕ) (hthree : 3 ≤ n) : SetLike (HessenbergIdeal n hthree) RealPlane where
  coe := fun ideal => ideal.carrier
  coe_injective := by
    intro first second heq
    have hparent : first.toRootSubset = second.toRootSubset := SetLike.coe_injective heq
    cases first
    cases second
    cases hparent
    rfl

namespace HessenbergIdeal

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A Hessenberg ideal is determined by its vectors. -/
@[ext] theorem ext {first second : HessenbergIdeal n hthree}
    (hmembers : ∀ alpha, alpha ∈ first ↔ alpha ∈ second) : first = second :=
  SetLike.ext hmembers

/-- The finite indexed ideal corresponding to a vector Hessenberg ideal. -/
def indexed (ideal : HessenbergIdeal n hthree) : HessenbergSpace n hthree where
  roots := ideal.toRootSubset.indicesFinset
  lower := by
    intro first second horder hmem
    rw [RootSubset.mem_indicesFinset] at hmem ⊢
    apply ideal.lower (alpha := positiveRootEquiv n first) (beta := positiveRootEquiv n second)
    · apply (rootOrder_indices _ _).mpr
      simpa only [PositiveRoot.index_equiv] using horder
    · exact hmem
  first_mem := by
    rw [RootSubset.mem_indicesFinset]
    change positiveRoot n (firstSimpleRootIndex n hthree) ∈ ideal.carrier
    simpa only [simpleRoot_zero, positiveRootEquiv_val] using ideal.first_mem
  second_mem := by
    rw [RootSubset.mem_indicesFinset]
    change positiveRoot n (secondSimpleRootIndex n hthree) ∈ ideal.carrier
    simpa only [simpleRoot_one, positiveRootEquiv_val] using ideal.second_mem

/-- Backend membership is precisely membership of the selected vector. -/
@[simp] theorem mem_indexed (ideal : HessenbergIdeal n hthree) (index : PositiveRootIndex n) :
    index ∈ ideal.indexed.roots ↔ positiveRoot n index ∈ ideal :=
  ideal.toRootSubset.mem_indicesFinset index

/-- An indexed lower ideal determines its positive-root subset. -/
def ofIndexed (ideal : HessenbergSpace n hthree) : HessenbergIdeal n hthree where
  toRootSubset := RootSubset.ofIndices (ideal.roots : Set (PositiveRootIndex n))
  lower := by
    intro alpha beta horder hmem
    change beta.val ∈ positiveRoot n '' (ideal.roots : Set (PositiveRootIndex n)) at hmem
    obtain ⟨index, hindex, heq⟩ := hmem
    have hequal : index = beta.index :=
      positiveRoot_injective n (heq.trans beta.index_val.symm)
    have hbeta : beta.index ∈ ideal.roots := hequal ▸ hindex
    have halpha := ideal.lower ((rootOrder_indices alpha beta).mp horder) hbeta
    exact ⟨alpha.index, halpha, alpha.index_val⟩
  first_mem := by
    exact ⟨firstSimpleRootIndex n hthree, ideal.first_mem,
      (congrArg Subtype.val (simpleRoot_zero n hthree)).symm⟩
  second_mem := by
    exact ⟨secondSimpleRootIndex n hthree, ideal.second_mem,
      (congrArg Subtype.val (simpleRoot_one n hthree)).symm⟩

/-- Passing from indices to vectors and back returns the indexed ideal. -/
@[simp] theorem indexed_ofIndexed (ideal : HessenbergSpace n hthree) :
    (ofIndexed ideal).indexed = ideal := by
  apply HessenbergSpace.ext
  ext index
  change index ∈ (RootSubset.ofIndices (ideal.roots : Set (PositiveRootIndex n))).indicesFinset ↔ _
  rw [RootSubset.mem_indicesFinset, ← RootSubset.mem_indices, RootSubset.indices_ofIndices]
  rfl

/-- Passing from vectors to indices and back returns the vector ideal. -/
@[simp] theorem ofIndexed_indexed (ideal : HessenbergIdeal n hthree) :
    ofIndexed ideal.indexed = ideal := by
  apply SetLike.coe_injective
  change positiveRoot n '' (ideal.indexed.roots : Set (PositiveRootIndex n)) = ideal.carrier
  have hindices : (ideal.indexed.roots : Set (PositiveRootIndex n)) =
      ideal.toRootSubset.indices := by
    ext index
    exact ideal.toRootSubset.mem_indicesFinset index
  rw [hindices]
  exact ideal.toRootSubset.image_indices

/-- Vector ideals and finite indexed ideals are equivalent. -/
def indexedEquiv : HessenbergIdeal n hthree ≃ HessenbergSpace n hthree where
  toFun := indexed
  invFun := ofIndexed
  left_inv := ofIndexed_indexed
  right_inv := indexed_ofIndexed

end HessenbergIdeal

end Schubert.DihedralSplines
