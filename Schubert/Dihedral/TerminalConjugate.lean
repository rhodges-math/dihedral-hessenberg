import Schubert.Dihedral.RootAlternatingWords
import Schubert.Dihedral.ReverseAlternatingConjugation
import Schubert.Dihedral.ReflectionIndex
import Mathlib.Tactic

/-! # Terminal conjugates of long alternating simple-root products -/

namespace Schubert.Dihedral

private theorem even_terminal_reflection (n half : ℕ) (hbound : 2 * half < n) :
    (positiveRootEquiv n ⟨2 * half, hbound⟩).reflection =
      DihedralGroup.sr (-(half : ZMod n)) := by
  have hquotient : 2 * half / 2 = half := by omega
  rw [PositiveRoot.reflection_equiv, rootReflection_eq_sr_of_even _ (by simp)]
  simp only [hquotient]

private theorem odd_terminal_reflection (n half : ℕ) (hbound : 2 * half + 1 < n) :
    (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection =
      DihedralGroup.sr ((half : ZMod n) + 1) := by
  have hquotient : (2 * half + 1) / 2 = half := by omega
  rw [PositiveRoot.reflection_equiv, rootReflection_eq_sr_of_odd _ (by simp)]
  simp only [hquotient]

private theorem complementary_cast (n half : ℕ) (hbound : 2 * half + 1 < n) :
    ((n - half - 1 : ℕ) : ZMod n) = -(half : ZMod n) - 1 := by
  have hsum : n - half - 1 + (half + 1) = n := by omega
  have hcast := congrArg (fun value : ℕ => (value : ZMod n)) hsum
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at hcast
  linear_combination hcast

/-- The first simple vector's ascent conjugate selects the terminal vector by witness parity. -/
theorem first_terminal_conjugate (n : ℕ) (hthree : 3 ≤ n) (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    let element := (simpleRoot n hthree 1).alternatingProduct
      (simpleRoot n hthree 0) (n - half - 1)
    element⁻¹ * (simpleRoot n hthree 0).reflection * element =
      if Even (n - half - 1) then (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection
        else (positiveRootEquiv n ⟨2 * half, by omega⟩).reflection := by
  dsimp only
  have hword : (simpleRoot n hthree 1).alternatingProduct
      (simpleRoot n hthree 0) (n - half - 1) =
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord 0 (Fin.rev 0) (n - half - 1)).reverse := by
    simpa [Fin.rev] using
      PositiveRoot.alternatingProduct_indexed n hthree 0 (n - half - 1)
  rw [hword, simpleRoot_reflection, conjugate_simple_reverse_alternatingWord]
  simp only
  split_ifs with heven
  · rw [odd_terminal_reflection, complementary_cast n half hbound]
    congr 1
    ring
  · rw [even_terminal_reflection, complementary_cast n half hbound]
    congr 1
    ring

/-- The second simple vector's ascent conjugate selects the opposite terminal vector. -/
theorem second_terminal_conjugate (n : ℕ) (hthree : 3 ≤ n) (half : ℕ)
    (hbound : 2 * half + 1 < n) :
    let element := (simpleRoot n hthree 0).alternatingProduct
      (simpleRoot n hthree 1) (n - half - 1)
    element⁻¹ * (simpleRoot n hthree 1).reflection * element =
      if Even (n - half - 1) then (positiveRootEquiv n ⟨2 * half, by omega⟩).reflection
        else (positiveRootEquiv n ⟨2 * half + 1, hbound⟩).reflection := by
  dsimp only
  have hword : (simpleRoot n hthree 0).alternatingProduct
      (simpleRoot n hthree 1) (n - half - 1) =
      (coxeterSystem n hthree).wordProd
        (CoxeterSystem.alternatingWord 1 (Fin.rev 1) (n - half - 1)).reverse := by
    simpa [Fin.rev] using
      PositiveRoot.alternatingProduct_indexed n hthree 1 (n - half - 1)
  rw [hword, simpleRoot_reflection, conjugate_simple_reverse_alternatingWord]
  simp only [ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  split_ifs with heven
  · rw [even_terminal_reflection, complementary_cast n half hbound]
    congr 1
    ring
  · rw [odd_terminal_reflection, complementary_cast n half hbound]
    congr 1
    ring

end Schubert.Dihedral
