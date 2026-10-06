import Schubert.Dihedral.PolynomialBasisAction
import Schubert.Dihedral.BinaryExponent
import Schubert.Dihedral.FrequencyFourier
import Schubert.FiniteGroupCharacters.WeightPairs

/-! # Cyclic weights of homogeneous polynomial degree representations -/

noncomputable section
namespace Schubert.Dihedral

/-- The positive rotation exponential is the standard cyclic additive character. -/
theorem rotation_exp_additive (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    Complex.exp (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) =
      ZMod.stdAddChar coordinate := by
  have hvalue := ZMod.stdAddChar_coe (N := n) (coordinate.val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hvalue
  rw [hvalue]
  congr 1
  push_cast
  ring

/-- The negative rotation exponential is the negative cyclic additive character. -/
theorem rotation_exp_neg_additive (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    Complex.exp (((-(2 * Real.pi * coordinate.val / n) : ℝ) : ℂ) * Complex.I) =
      ZMod.stdAddChar (-coordinate) := by
  have hvalue := ZMod.stdAddChar_coe (N := n) (-(coordinate.val : ℤ))
  simp only [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val] at hvalue
  rw [hvalue]
  congr 1
  push_cast
  ring

/-- An auxiliary monomial has the difference of its exponent coordinates as cyclic weight. -/
theorem rotation_monomial_additive (n : ℕ) [NeZero n] (coordinate : ZMod n)
    (first second : ℕ) :
    Complex.exp (((-(2 * Real.pi * coordinate.val / n) : ℝ) : ℂ) * Complex.I) ^ first *
      Complex.exp (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) ^ second =
        ZMod.stdAddChar (((second : ZMod n) - (first : ZMod n)) * coordinate) := by
  rw [rotation_exp_neg_additive, rotation_exp_additive]
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- The polynomial rotation character lists all weights from its degree to its negative. -/
theorem polynomialPiece_character_weights (n : ℕ) [NeZero n]
    (degree : ℕ) (coordinate : ZMod n) :
    (polynomialPieceFDRep n degree).character (.r coordinate) =
      ∑ index : Fin (degree + 1),
        ZMod.stdAddChar ((((degree : ℤ) - 2 * index.val : ℤ) : ZMod n) * coordinate) := by
  classical
  let := FiniteDimensional.fintypeBasisIndex (auxiliaryPieceBasis degree)
  rw [polynomialPiece_character_r]
  apply Fintype.sum_equiv (binaryExponentEquiv degree)
  intro exponent
  rw [rotation_monomial_additive]
  apply congrArg (ZMod.stdAddChar (N := n))
  change ((exponent.val 1 : ZMod n) - (exponent.val 0 : ZMod n)) * coordinate =
    (((degree : ℤ) - 2 * exponent.val 0 : ℤ) : ZMod n) * coordinate
  have hdegree : degree = exponent.val 0 + exponent.val 1 :=
    exponent.property.symm.trans (binaryExponent_degree exponent.val)
  have hcast : (degree : ZMod n) = (exponent.val 0 : ZMod n) + (exponent.val 1 : ZMod n) := by
    simpa only [Nat.cast_add] using congrArg (fun value : ℕ => (value : ZMod n)) hdegree
  push_cast
  rw [hcast]
  ring

/-- Opposite monomial weights pair into the frequency rotation characters. -/
theorem polynomialPiece_character_r_pairs (n : ℕ) [NeZero n]
    (degree : ℕ) (coordinate : ZMod n) :
    (polynomialPieceFDRep n degree).character (.r coordinate) =
      (∑ index : Fin ((degree + 1) / 2),
        (frequencyFDRep n (degree - 2 * index.val : ℕ)).character (.r coordinate)) +
      if Even degree then 1 else 0 := by
  classical
  rw [polynomialPiece_character_weights]
  rw [Schubert.FiniteGroupCharacters.sum_weight_pairs
    (fun weight : ℤ => ZMod.stdAddChar ((weight : ZMod n) * coordinate)) degree]
  simp only [Int.cast_neg, Int.cast_zero, neg_mul, zero_mul, AddChar.map_zero_eq_one]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  rw [Frequency.character_additive]
  have hbound := index.isLt
  have hweight : (degree : ℤ) - 2 * index.val = ((degree - 2 * index.val : ℕ) : ℤ) := by
    omega
  rw [hweight]
  simp only [Int.cast_natCast]

end Schubert.Dihedral
