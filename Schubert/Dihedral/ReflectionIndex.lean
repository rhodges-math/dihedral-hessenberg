import Schubert.Dihedral.Group
import Mathlib.Data.Nat.ModEq
import Lean.Elab.Tactic.Omega

/-!
# Positive-root indices and the reflections of a dihedral group

The alternating-word numbering of root reflections is a bijection between
positive-root indices and the concrete elements `sr j`. Its coordinate in
`ZMod n` is negative on even indices and positive on odd indices.
-/

namespace Schubert.Dihedral

/-- The coordinate of a numbered positive-root reflection in the `sr` constructor. -/
def reflectionCoordinate {n : ℕ} (i : PositiveRootIndex n) : ZMod n :=
  if i.val % 2 = 0 then -((i.val / 2 : ℕ) : ZMod n) else (i.val / 2 + 1 : ℕ)

theorem rootReflection_eq_sr_of_even {n : ℕ} (i : PositiveRootIndex n)
    (heven : i.val % 2 = 0) :
    rootReflection i = DihedralGroup.sr (-((i.val / 2 : ℕ) : ZMod n)) := by
  rw [rootReflection_of_even_index i heven, rotation_eq_r_one,
    firstSimpleReflection, DihedralGroup.r_pow, one_mul,
    DihedralGroup.r_mul_sr, zero_sub]

theorem rootReflection_eq_sr_of_odd {n : ℕ} (i : PositiveRootIndex n)
    (hodd : i.val % 2 ≠ 0) :
    rootReflection i = DihedralGroup.sr (((i.val / 2 : ℕ) : ZMod n) + 1) := by
  rw [rootReflection_of_odd_index i hodd, secondSimpleReflection,
    firstSimpleReflection, DihedralGroup.sr_mul_sr, zero_sub,
    DihedralGroup.r_pow, DihedralGroup.r_mul_sr]
  congr 1
  ring

/-- The indexed reflection has its explicit `sr` coordinate. -/
theorem rootReflection_eq_sr {n : ℕ} (i : PositiveRootIndex n) :
    rootReflection i = DihedralGroup.sr (reflectionCoordinate i) := by
  unfold reflectionCoordinate
  split_ifs with heven
  · exact rootReflection_eq_sr_of_even i heven
  · simpa only [Nat.cast_add, Nat.cast_one] using rootReflection_eq_sr_of_odd i heven

private theorem natCast_injective_below_modulus {n a b : ℕ}
    (ha : a < n) (hb : b < n) (heq : (a : ZMod n) = (b : ZMod n)) : a = b := by
  have hvalue := congrArg ZMod.val heq
  rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] at hvalue
  exact hvalue

theorem reflectionCoordinate_even_ne_odd {n : ℕ} (i j : PositiveRootIndex n)
    (heven : i.val % 2 = 0) (hodd : j.val % 2 ≠ 0) :
    reflectionCoordinate i ≠ reflectionCoordinate j := by
  intro heq
  rw [reflectionCoordinate, ite_eq_left heven, reflectionCoordinate,
    ite_eq_right hodd] at heq
  have hzero : ((i.val / 2 + (j.val / 2 + 1) : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_add, ← heq, add_neg_cancel]
  have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hsmall : i.val / 2 + (j.val / 2 + 1) < n := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  have hsum := Nat.eq_zero_of_dvd_of_lt hdiv hsmall
  omega

/-- The concrete reflection coordinate uniquely determines its positive-root index. -/
theorem reflectionCoordinate_injective (n : ℕ) :
    Function.Injective (reflectionCoordinate (n := n)) := by
  intro i j heq
  by_cases hi : i.val % 2 = 0
  · by_cases hj : j.val % 2 = 0
    · rw [reflectionCoordinate, ite_eq_left hi, reflectionCoordinate,
        ite_eq_left hj] at heq
      have hquot := natCast_injective_below_modulus
        (lt_of_le_of_lt (Nat.div_le_self _ _) i.isLt)
        (lt_of_le_of_lt (Nat.div_le_self _ _) j.isLt) (neg_injective heq)
      apply Fin.ext
      omega
    · exact (reflectionCoordinate_even_ne_odd i j hi hj heq).elim
  · by_cases hj : j.val % 2 = 0
    · exact (reflectionCoordinate_even_ne_odd j i hj hi heq.symm).elim
    · rw [reflectionCoordinate, ite_eq_right hi, reflectionCoordinate,
        ite_eq_right hj] at heq
      have hiBound : i.val / 2 + 1 < n := by
        have := i.isLt
        omega
      have hjBound : j.val / 2 + 1 < n := by
        have := j.isLt
        omega
      have hquot := natCast_injective_below_modulus hiBound hjBound heq
      apply Fin.ext
      omega

/-- Numbered positive-root reflections are pairwise distinct. -/
theorem rootReflection_injective (n : ℕ) :
    Function.Injective (rootReflection (n := n)) := by
  intro i j heq
  rw [rootReflection_eq_sr, rootReflection_eq_sr] at heq
  exact reflectionCoordinate_injective n (DihedralGroup.sr.inj heq)

/-- Every concrete reflection is the reflection of a numbered positive root. -/
theorem exists_rootReflection_eq_sr (n : ℕ) (hthree : 3 ≤ n) (j : ZMod n) :
    ∃ i : PositiveRootIndex n, rootReflection i = DihedralGroup.sr j := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  have hbijective := (reflectionCoordinate_injective n).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_fin])
  obtain ⟨i, hi⟩ := hbijective.2 j
  exact ⟨i, by rw [rootReflection_eq_sr, hi]⟩

end Schubert.Dihedral
