import DihedralHessenberg.Dihedral.RootCosetObjects
import DihedralHessenberg.Dihedral.SimpleRootObjects
import DihedralHessenberg.Dihedral.CoxeterSystem

/-! # The minimal simple-root generating pair -/

namespace Schubert.Dihedral

/-- The two simple-root reflections generate the whole dihedral group. -/
theorem simple_roots_generate (n : ℕ) (hthree : 3 ≤ n) :
    Subgroup.closure {(simpleRoot n hthree 0).reflection,
      (simpleRoot n hthree 1).reflection} = ⊤ := by
  have hrange : Set.range (coxeterSystem n hthree).simple =
      {(simpleRoot n hthree 0).reflection, (simpleRoot n hthree 1).reflection} := by
    ext element
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨simple, rfl⟩
      fin_cases simple
      · exact Or.inl (by rw [simpleRoot_reflection, coxeterSystem_simple]; rfl)
      · exact Or.inr (by rw [simpleRoot_reflection, coxeterSystem_simple]; rfl)
    · rintro (rfl | rfl)
      · exact ⟨0, by rw [coxeterSystem_simple, simpleRoot_reflection]⟩
      · exact ⟨1, by rw [coxeterSystem_simple, simpleRoot_reflection]⟩
  rw [← hrange]
  exact (coxeterSystem n hthree).subgroup_closure_range_simple

/-- A single root reflection generates a proper subgroup for at least three sides. -/
theorem PositiveRoot.subgroup_ne_top {n : ℕ} (hthree : 3 ≤ n) (alpha : PositiveRoot n) :
    alpha.subgroup ≠ ⊤ := by
  intro heq
  let : NeZero n := ⟨by omega⟩
  have hcard := alpha.card_subgroup
  rw [heq, Subgroup.card_top, Nat.card_eq_fintype_card, DihedralGroup.card] at hcard
  omega

end Schubert.Dihedral
