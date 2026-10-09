import DihedralHessenberg.Dihedral.RootRescaling
import DihedralHessenberg.Dihedral.Conjugacy
import DihedralHessenberg.Dihedral.SimpleRootObjects

/-! # Positive radii constant on reflection conjugacy classes -/

noncomputable section

open scoped Classical

namespace Schubert.Dihedral.PositiveRoot

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The two prescribed radii are assigned by conjugacy to the first simple reflection. -/
def classRadius (hthree : 3 ≤ n) (first second : ℝ) (alpha : PositiveRoot n) : ℝ :=
  if IsConj alpha.reflection (simpleRoot n hthree 0).reflection then first else second

/-- Positive class radii give positive length on every positive direction. -/
theorem classRadius_pos (first second : ℝ) (hfirst : 0 < first) (hsecond : 0 < second)
    (alpha : PositiveRoot n) : 0 < classRadius hthree first second alpha := by
  unfold classRadius
  split_ifs <;> assumption

/-- Conjugate reflections receive the same prescribed radius. -/
theorem classRadius_conj (first second : ℝ) (alpha beta : PositiveRoot n)
    (hconj : IsConj alpha.reflection beta.reflection) :
    classRadius hthree first second alpha = classRadius hthree first second beta := by
  have hequiv : IsConj alpha.reflection (simpleRoot n hthree 0).reflection ↔
      IsConj beta.reflection (simpleRoot n hthree 0).reflection :=
    ⟨fun h => hconj.symm.trans h, fun h => hconj.trans h⟩
  simp only [classRadius, hequiv]

/-- For an even polygon, the numbered radius is determined by reflection-coordinate parity. -/
theorem classRadius_numbered [NeZero n] (heven : Even n) (first second : ℝ)
    (index : PositiveRootIndex n) :
    classRadius hthree first second (positiveRootEquiv n index) =
      if (reflectionCoordinate index).val % 2 = 0 then first else second := by
  unfold classRadius
  rw [reflection_equiv, simpleRoot_reflection, simpleReflection_zero,
    firstSimpleReflection, rootReflection_eq_sr,
    isConj_sr_iff_val_parity_of_even n heven]
  simp only [ZMod.val_zero, Nat.zero_mod]

/-- The B/C numbered short-class positions are the first and fourth directions. -/
theorem classRadius_four (first second : ℝ) (index : PositiveRootIndex 4) :
    classRadius (by decide : 3 ≤ 4) first second (positiveRootEquiv 4 index) =
      if index.val = 0 ∨ index.val = 3 then first else second := by
  rw [classRadius_numbered (by decide : Even 4)]
  fin_cases index <;> norm_num [reflectionCoordinate, ZMod.val_one_eq_one_mod,
    ZMod.val_ofNat, ZMod.neg_val']

/-- The G short class consists of the first, fourth, and fifth directions. -/
theorem classRadius_six (first second : ℝ) (index : PositiveRootIndex 6) :
    classRadius (by decide : 3 ≤ 6) first second (positiveRootEquiv 6 index) =
      if index.val = 0 ∨ index.val = 3 ∨ index.val = 4 then first else second := by
  rw [classRadius_numbered (by decide : Even 6)]
  fin_cases index <;> norm_num [reflectionCoordinate, ZMod.val_one_eq_one_mod,
    ZMod.val_ofNat, ZMod.neg_val']

end Schubert.Dihedral.PositiveRoot
