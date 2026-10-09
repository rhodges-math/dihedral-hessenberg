import DihedralHessenberg.Dihedral.FrequencyRepresentation
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! # Additive-character formulas for dihedral frequency traces -/

noncomputable section

open scoped BigOperators

namespace Schubert.Dihedral.Frequency

/-- The standard cyclic additive character and its negative have the cosine sum. -/
theorem additive_pair (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    ZMod.stdAddChar coordinate + ZMod.stdAddChar (-coordinate) =
      2 * (Real.cos (2 * Real.pi * coordinate.val / n) : ℂ) := by
  have hpositive := ZMod.stdAddChar_coe (N := n) (coordinate.val : ℤ)
  have hnegative := ZMod.stdAddChar_coe (N := n) (-(coordinate.val : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] at hpositive hnegative
  rw [hpositive, hnegative, Complex.ofReal_cos, Complex.cos]
  push_cast
  have hfirst : 2 * (Real.pi : ℂ) * Complex.I * coordinate.val / n =
      (2 * (Real.pi : ℂ) * coordinate.val / n) * Complex.I := by ring
  have hsecond : 2 * (Real.pi : ℂ) * Complex.I * -(coordinate.val : ℂ) / n =
      -(2 * (Real.pi : ℂ) * coordinate.val / n) * Complex.I := by ring
  rw [hfirst, hsecond]
  ring

/-- Every frequency rotation trace is the sum of a cyclic additive character and its negative. -/
theorem character_additive (n : ℕ) [NeZero n] (frequency coordinate : ZMod n) :
    (frequencyFDRep n frequency).character (.r coordinate) =
      ZMod.stdAddChar (frequency * coordinate) + ZMod.stdAddChar (-(frequency * coordinate)) := by
  rw [frequencyFDRep_character, frequencyRepresentation_character_r, additive_pair]

/-- The sum over all cyclic frequencies vanishes away from the identity rotation. -/
theorem additive_sum (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    ∑ frequency : ZMod n, ZMod.stdAddChar (coordinate * frequency) =
      if coordinate = 0 then (n : ℂ) else 0 := by
  classical
  by_cases hzero : coordinate = 0
  · simp [hzero]
  · rw [ite_eq_right hzero]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar n hzero)

/-- The even cyclic midpoint has additive-character value minus one. -/
theorem additive_midpoint (n : ℕ) [NeZero n] (heven : Even n) :
    ZMod.stdAddChar (N := n) (n / 2 : ℕ) = -1 := by
  have hvalue := ZMod.stdAddChar_coe (N := n) (n / 2 : ℕ)
  simp only [Int.cast_natCast] at hvalue
  rw [hvalue]
  have hhalf : (2 : ℂ) * (n / 2 : ℕ) = n := by
    exact_mod_cast Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hangle : 2 * (Real.pi : ℂ) * Complex.I * (n / 2 : ℕ) / n =
      (Real.pi : ℂ) * Complex.I := by
    calc
      _ = ((Real.pi : ℂ) * Complex.I) * ((2 : ℂ) * (n / 2 : ℕ)) / n := by ring
      _ = _ := by rw [hhalf]; field_simp [hnzero]
  rw [hangle, Complex.exp_pi_mul_I]

/-- The midpoint frequency evaluates any rotation by its coordinate parity. -/
theorem additive_midpoint_mul (n : ℕ) [NeZero n] (heven : Even n) (coordinate : ZMod n) :
    ZMod.stdAddChar (((n / 2 : ℕ) : ZMod n) * coordinate) =
      (-1 : ℂ) ^ coordinate.val := by
  rw [← ZMod.natCast_zmod_val coordinate, mul_comm, ← nsmul_eq_mul,
    AddChar.map_nsmul_eq_pow, additive_midpoint n heven]
  simp only [ZMod.natCast_zmod_val]

end Schubert.Dihedral.Frequency
