import Schubert.Dihedral.BlockSubgroup

/-! # Equivariant standard cosets of alternating-block orbits -/

namespace Schubert.Dihedral

open scoped Pointwise

private theorem orbit_cosets {G X : Type*} [Group G] [MulAction G X] (value : X)
    (subgroup : Subgroup G) (hsubgroup : MulAction.stabilizer G value = subgroup) :
    ∃ equivalence : (G ⧸ subgroup) ≃ MulAction.orbit G value,
      ∀ (element : G) (coset : G ⧸ subgroup),
        equivalence (element • coset) = element • equivalence coset := by
  subst subgroup
  refine ⟨(MulAction.orbitEquivQuotientStabilizer G value).symm, ?_⟩
  intro element coset
  apply Subtype.ext
  exact MulAction.ofQuotientStabilizer_smul G value element coset

/-- Standard terminal-root cosets equivariantly parametrize the first block orbit. -/
theorem first_block_cosets {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    ∃ equivalence : (positiveRootEquiv n ⟨2 * half, by omega⟩).Cosets ≃
        MulAction.orbit (DihedralGroup n)
          (alternatingBlock 1 (simpleRoot n hthree 0) (simpleRoot n hthree 1) half),
      ∀ (element : DihedralGroup n) coset,
        equivalence (element • coset) = element • equivalence coset := by
  exact orbit_cosets _ _ (first_block_subgroup (hthree := hthree) half hbound)

/-- Standard terminal-root cosets equivariantly parametrize the second block orbit. -/
theorem second_block_cosets {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    ∃ equivalence : (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).Cosets ≃
        MulAction.orbit (DihedralGroup n)
          (alternatingBlock 1 (simpleRoot n hthree 1) (simpleRoot n hthree 0) half),
      ∀ (element : DihedralGroup n) coset,
        equivalence (element • coset) = element • equivalence coset := by
  exact orbit_cosets _ _ (second_block_subgroup (hthree := hthree) half hbound)

end Schubert.Dihedral
