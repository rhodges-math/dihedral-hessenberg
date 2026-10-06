import Schubert.Dihedral.Group
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Tactic.FinCases

/-!
# The rank-two Coxeter presentation of a dihedral group

The simple generators of the Coxeter matrix `I (n - 2)` map to the distinguished
reflections `sr 0` and `sr 1` of `DihedralGroup n`. Their product has order `n`,
both in the concrete group and in the Coxeter presentation.
-/

namespace Schubert.Dihedral

theorem coxeterMatrix_apply_of_ne (n : ℕ) (hthree : 3 ≤ n) {i j : Fin 2}
    (hne : i ≠ j) : CoxeterMatrix.I (n - 2) i j = n := by
  change (if i = j then 1 else n - 2 + 2) = n
  rw [ite_eq_right hne, Nat.sub_add_cancel (le_trans (by decide : 2 ≤ 3) hthree)]

/-- The distinguished reflections satisfy the rank-two Coxeter relations. -/
theorem simpleReflection_isLiftable (n : ℕ) (hthree : 3 ≤ n) :
    (CoxeterMatrix.I (n - 2)).IsLiftable (simpleReflection n) := by
  intro i j
  by_cases heq : i = j
  · subst j
    rw [(CoxeterMatrix.I (n - 2)).diagonal, simpleReflection_mul_self, one_pow]
  · rw [coxeterMatrix_apply_of_ne n hthree heq]
    fin_cases i <;> fin_cases j
    · exact (heq rfl).elim
    · simpa [simpleReflection, rotation] using rotation_pow_eq_one n
    · have hreverse : (secondSimpleReflection n * firstSimpleReflection n) ^ n = 1 := by
        rw [secondSimpleReflection, firstSimpleReflection, DihedralGroup.sr_mul_sr]
        simp only [DihedralGroup.r_pow, ZMod.natCast_self, mul_zero, DihedralGroup.r_zero]
      simpa [simpleReflection] using hreverse
    · exact (heq rfl).elim

/-- The homomorphism from the rank-two Coxeter presentation to the concrete dihedral group. -/
def presentationToGroup (n : ℕ) (hthree : 3 ≤ n) :
    (CoxeterMatrix.I (n - 2)).Group →* DihedralGroup n :=
  (CoxeterMatrix.I (n - 2)).toCoxeterSystem.lift
    ⟨simpleReflection n, simpleReflection_isLiftable n hthree⟩

theorem presentationToGroup_simple (n : ℕ) (hthree : 3 ≤ n) (i : Fin 2) :
    presentationToGroup n hthree ((CoxeterMatrix.I (n - 2)).simple i) =
      simpleReflection n i :=
  (CoxeterMatrix.I (n - 2)).toCoxeterSystem.lift_apply_simple
    (simpleReflection_isLiftable n hthree) i

/-- The product of the presentation's two simple generators has order `n`. -/
theorem orderOf_presentation_simple_mul_simple (n : ℕ) (hthree : 3 ≤ n) :
    orderOf ((CoxeterMatrix.I (n - 2)).simple 0 *
      (CoxeterMatrix.I (n - 2)).simple 1) = n := by
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    have hrelation :=
      (CoxeterMatrix.I (n - 2)).toCoxeterSystem.simple_mul_simple_pow 0 1
    rw [CoxeterMatrix.toCoxeterSystem_simple,
      coxeterMatrix_apply_of_ne n hthree (by decide : (0 : Fin 2) ≠ 1)] at hrelation
    exact hrelation
  · have hdiv := orderOf_map_dvd (presentationToGroup n hthree)
      ((CoxeterMatrix.I (n - 2)).simple 0 * (CoxeterMatrix.I (n - 2)).simple 1)
    rw [map_mul, presentationToGroup_simple, presentationToGroup_simple,
      simpleReflection_zero, simpleReflection_one, ← rotation,
      rotation_eq_r_one, DihedralGroup.orderOf_r_one] at hdiv
    exact hdiv

/-- The two simple generators generate the rank-two Coxeter presentation as a group. -/
theorem presentation_simple_generators (n : ℕ) :
    Subgroup.closure ({(CoxeterMatrix.I (n - 2)).simple 0,
      (CoxeterMatrix.I (n - 2)).simple 1} :
      Set (CoxeterMatrix.I (n - 2)).Group) = ⊤ := by
  have hrange : Set.range (CoxeterMatrix.I (n - 2)).simple =
      {(CoxeterMatrix.I (n - 2)).simple 0, (CoxeterMatrix.I (n - 2)).simple 1} := by
    ext element
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · intro hmember
      rcases hmember with hzero | hone
      · exact ⟨0, hzero.symm⟩
      · exact ⟨1, hone.symm⟩
  rw [← hrange, ← CoxeterMatrix.toCoxeterSystem_simple]
  exact (CoxeterMatrix.I (n - 2)).toCoxeterSystem.subgroup_closure_range_simple

end Schubert.Dihedral
