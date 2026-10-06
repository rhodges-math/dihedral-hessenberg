import Schubert.DihedralSplines.ChamberIdeal
import Schubert.Dihedral.HexagonDepthIdeal

/-! # Four-root cone ideals and reflection carriers -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- Every four-vector cone ideal has exactly the first four root reflections. -/
theorem six_four_reflections (ideal : HessenbergIdeal 6 (by decide))
    (hcard : ideal.carrier.ncard = 4) :
    PositiveRoot.reflection '' {alpha : PositiveRoot 6 | alpha.val ∈ ideal.carrier} =
      {(positiveRootEquiv 6 ⟨0, by decide⟩).reflection,
        (positiveRootEquiv 6 ⟨1, by decide⟩).reflection,
        (positiveRootEquiv 6 ⟨2, by decide⟩).reflection,
        (positiveRootEquiv 6 ⟨3, by decide⟩).reflection} := by
  have hindexed : ideal.indexed.roots.card = 4 := ideal.ncard_indexed.symm.trans hcard
  have hprefix : ∀ index : Fin 6, index ∈ ideal.indexed.roots ↔ index.val < 4 := by
    rcases ideal.indexed.root_membership_classification with hprefix | ⟨hodd, _, _⟩
    · simpa only [hindexed] using hprefix
    · rw [hindexed] at hodd
      exact (by decide : ¬Odd 4) hodd |>.elim
  have hmember (index : Fin 6) : (positiveRootEquiv 6 index).val ∈ ideal.carrier ↔
      index.val < 4 := (ideal.mem_indexed index).symm.trans (hprefix index)
  ext reflection
  constructor
  · rintro ⟨alpha, halpha, rfl⟩
    obtain ⟨index, rfl⟩ := (positiveRootEquiv 6).surjective alpha
    have hindex := (hmember index).mp halpha
    fin_cases index
    all_goals simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals tauto
  · intro hreflection
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hreflection
    rcases hreflection with rfl | rfl | rfl | rfl
    · exact ⟨positiveRootEquiv 6 ⟨0, by decide⟩, (hmember _).mpr (by decide), rfl⟩
    · exact ⟨positiveRootEquiv 6 ⟨1, by decide⟩, (hmember _).mpr (by decide), rfl⟩
    · exact ⟨positiveRootEquiv 6 ⟨2, by decide⟩, (hmember _).mpr (by decide), rfl⟩
    · exact ⟨positiveRootEquiv 6 ⟨3, by decide⟩, (hmember _).mpr (by decide), rfl⟩

end Schubert.DihedralSplines
