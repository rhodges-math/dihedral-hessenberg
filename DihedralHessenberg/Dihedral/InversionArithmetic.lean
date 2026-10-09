import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Basic

/-! # Numerical comparisons for the concrete dihedral inversion bridge -/

namespace Schubert.Dihedral

/-- The shorter odd distance decreases the rotation distance in the negative half-turn. -/
theorem rotation_reflection_distance_lt_iff (n position exponent : ℕ)
    (hposition : position < n) (hexponent : exponent < n) :
    (if (position + exponent) % n = 0 then 1 else
      min (2 * ((position + exponent) % n) + 1)
        (2 * (n - (position + exponent) % n) - 1)) <
        2 * min exponent (n - exponent) ↔
      n ≤ (position + 2 * exponent) % (2 * n) := by
  have hmod : (position + exponent) % n =
      if position + exponent < n then position + exponent else position + exponent - n := by
    by_cases hsmall : position + exponent < n
    · simp only [ite_eq_left hsmall, Nat.mod_eq_of_lt hsmall]
    · rw [ite_eq_right hsmall, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hangle : (position + 2 * exponent) % (2 * n) =
      if position + 2 * exponent < 2 * n then position + 2 * exponent
        else position + 2 * exponent - 2 * n := by
    by_cases hsmall : position + 2 * exponent < 2 * n
    · simp only [ite_eq_left hsmall, Nat.mod_eq_of_lt hsmall]
    · rw [ite_eq_right hsmall, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod, hangle]
  split_ifs <;> omega

/-- The shorter even distance decreases the reflection distance in its negative half-turn. -/
theorem reflection_rotation_distance_lt_iff (n position exponent : ℕ)
    (hposition : position < n) (hexponent : exponent < n) :
    2 * min ((position + exponent) % n) (n - (position + exponent) % n) <
      (if exponent = 0 then 1 else min (2 * exponent - 1) (2 * (n - exponent) + 1)) ↔
      (position + 2 * exponent) % (2 * n) = 0 ∨
        n < (position + 2 * exponent) % (2 * n) := by
  have hmod : (position + exponent) % n =
      if position + exponent < n then position + exponent else position + exponent - n := by
    by_cases hsmall : position + exponent < n
    · simp only [ite_eq_left hsmall, Nat.mod_eq_of_lt hsmall]
    · rw [ite_eq_right hsmall, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  have hangle : (position + 2 * exponent) % (2 * n) =
      if position + 2 * exponent < 2 * n then position + 2 * exponent
        else position + 2 * exponent - 2 * n := by
    by_cases hsmall : position + 2 * exponent < 2 * n
    · simp only [ite_eq_left hsmall, Nat.mod_eq_of_lt hsmall]
    · rw [ite_eq_right hsmall, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod, hangle]
  split_ifs <;> omega

end Schubert.Dihedral
