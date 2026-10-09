import DihedralHessenberg.Dihedral.FrequencyFourier

/-! # Powers of the primitive rotation character -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.Frequency

/-- The standard additive character is the corresponding power of the primitive rotation value. -/
theorem additive_exp (n : ℕ) [NeZero n] (coordinate : ZMod n) :
    ZMod.stdAddChar coordinate =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val := by
  have hvalue := ZMod.stdAddChar_coe (N := n) (coordinate.val : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hvalue
  rw [hvalue, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Scaling a cyclic coordinate raises its additive-character value to that natural power. -/
theorem additive_nat_mul (n : ℕ) [NeZero n] (degree : ℕ) (coordinate : ZMod n) :
    ZMod.stdAddChar ((degree : ZMod n) * coordinate) =
      ZMod.stdAddChar coordinate ^ degree := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

end Schubert.Dihedral.Frequency
