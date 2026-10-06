import Schubert.Dihedral.Group
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.LinearCombination

/-! # Commuting coordinates and the doubling kernel for even dihedral groups -/

namespace Schubert.Dihedral

/-- A rotation commutes with a reflection exactly when twice its coordinate is zero. -/
theorem commute_r_sr_iff (n : ℕ) (first second : ZMod n) :
    Commute (DihedralGroup.r first) (DihedralGroup.sr second) ↔ first + first = 0 := by
  change (DihedralGroup.r first * DihedralGroup.sr second =
    DihedralGroup.sr second * DihedralGroup.r first) ↔ _
  simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq]
  constructor <;> intro heq <;> linear_combination -heq

/-- A reflection commutes with a rotation exactly when twice the rotation coordinate is zero. -/
theorem commute_sr_r_iff (n : ℕ) (first second : ZMod n) :
    Commute (DihedralGroup.sr first) (DihedralGroup.r second) ↔ second + second = 0 := by
  exact ⟨fun h => (commute_r_sr_iff n second first).mp h.symm,
    fun h => ((commute_r_sr_iff n second first).mpr h).symm⟩

/-- Two reflections commute exactly when twice their coordinate difference is zero. -/
theorem commute_sr_sr_iff (n : ℕ) (first second : ZMod n) :
    Commute (DihedralGroup.sr first) (DihedralGroup.sr second) ↔
      (second - first) + (second - first) = 0 := by
  change (DihedralGroup.sr first * DihedralGroup.sr second =
    DihedralGroup.sr second * DihedralGroup.sr first) ↔ _
  simp only [DihedralGroup.sr_mul_sr, DihedralGroup.r.injEq]
  constructor <;> intro heq <;> linear_combination heq

/-- For positive even n, the doubling kernel consists of zero and the half-turn coordinate. -/
theorem add_self_eq_zero_iff_of_even (n : ℕ) [NeZero n] (heven : Even n) (coordinate : ZMod n) :
    coordinate + coordinate = 0 ↔ coordinate = 0 ∨ coordinate = (n / 2 : ℕ) := by
  have hnpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnmod := Nat.even_iff.mp heven
  have hbound : n / 2 < n := by omega
  have hhalfVal : ((n / 2 : ℕ) : ZMod n).val = n / 2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
  rw [← neg_eq_iff_add_eq_zero, ZMod.neg_eq_self_iff]
  constructor
  · rintro (hzero | hdouble)
    · exact Or.inl hzero
    · apply Or.inr
      have hvalue : coordinate.val = n / 2 := by omega
      rw [← ZMod.natCast_zmod_val coordinate, hvalue]
  · rintro (hzero | rfl)
    · exact Or.inl hzero
    · exact Or.inr (by rw [hhalfVal]; omega)

/-- The doubling kernel in ZMod n has two elements for positive even n. -/
theorem card_add_self_eq_zero_of_even (n : ℕ) [NeZero n] (heven : Even n) :
    Nat.card {coordinate : ZMod n // coordinate + coordinate = 0} = 2 := by
  classical
  have hnpositive : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnmod := Nat.even_iff.mp heven
  have hbound : n / 2 < n := by omega
  have hhalfVal : ((n / 2 : ℕ) : ZMod n).val = n / 2 := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hbound]
  have hdistinct : (0 : ZMod n) ≠ (n / 2 : ℕ) := by
    intro heq
    have hvalues := congrArg ZMod.val heq
    rw [ZMod.val_zero, hhalfVal] at hvalues
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfilter : (Finset.univ.filter fun coordinate : ZMod n =>
      coordinate + coordinate = 0) = {0, ((n / 2 : ℕ) : ZMod n)} := by
    ext coordinate
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, add_self_eq_zero_iff_of_even n heven]
  rw [hfilter, Finset.card_pair hdistinct]

end Schubert.Dihedral
