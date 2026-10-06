import Schubert.Dihedral.RootNoLoops
import Schubert.DihedralSplines.PaperLocalization

/-! # Boundary roots of a singleton vertex -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

/-- Every selected root is an outgoing boundary root of a singleton vertex. -/
theorem singleton_boundary (n : ℕ) (selected : RootSubset n)
    (vertex : DihedralGroup n) (alpha : PositiveRoot n) :
    alpha ∈ selected.boundaryRoots {vertex} vertex ↔ alpha.val ∈ selected := by
  rw [mem_boundaryRoots]
  have hmove : vertex * alpha.reflection ≠ vertex := by
    intro heq
    apply alpha.reflection_ne_one
    exact mul_left_cancel (heq.trans (mul_one vertex).symm)
  simp only [Set.mem_singleton_iff, hmove, not_false_eq_true, and_true]

/-- A singleton boundary contains exactly as many roots as the selected vector subset. -/
theorem card_singleton_boundary (n : ℕ) (selected : RootSubset n)
    (vertex : DihedralGroup n) :
    (selected.boundaryRoots {vertex} vertex).card = selected.carrier.ncard := by
  classical
  have himage : Subtype.val '' (selected.boundaryRoots {vertex} vertex : Set (PositiveRoot n)) =
      selected.carrier := by
    ext vector
    constructor
    · rintro ⟨alpha, hmem, rfl⟩
      exact (singleton_boundary n selected vertex alpha).mp hmem
    · intro hmem
      exact ⟨selected.root vector hmem,
        (singleton_boundary n selected vertex _).mpr hmem, rfl⟩
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset]

end Schubert.Dihedral.RootSubset
