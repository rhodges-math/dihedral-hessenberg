import Schubert.DihedralSplines.FullRightTrace
import Schubert.Dihedral.VectorDenominator
import Schubert.Dihedral.FrequencyPowerCharacter
import Schubert.Dihedral.PolynomialDecomposition
import Schubert.Dihedral.RotationFourierSums
import Schubert.Splines.GeometricTrace
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Determinant identity for the full right quotient traces -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral
variable (n : ℕ) [NeZero n] (hthree : 3 ≤ n)

include hthree in
private theorem vector_pair (coordinate : ZMod n) :
    let root := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
    (vectorRepresentation n).character (.r coordinate) =
      root⁻¹ ^ coordinate.val + root ^ coordinate.val := by
  have hi : Nonempty (coinvariantPieceFDRep n 1 ≅ frequencyFDRep n (1 : ZMod n)) := by
    simpa only [Nat.cast_one] using
      Coinvariant.Middle.frequency_iso n hthree 1 (by omega) (by omega)
  have h := congrFun (FDRep.char_iso (hi.some ≪≫ (frequency_one_iso n).some)) (.r coordinate)
  rw [Coinvariant.Middle.character_r n hthree 1 (by omega) (by omega)] at h
  simpa only [FDRep.character_of, pow_one] using h.symm

include hthree in
private theorem vector_factor (coordinate : ZMod n) :
    let root := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
    vectorDenominator n (.r coordinate) =
      (1 - Polynomial.C (root⁻¹ ^ coordinate.val) * Polynomial.X) *
      (1 - Polynomial.C (root ^ coordinate.val) * Polynomial.X) := by
  rw [vectorDenominator_trace, vector_pair n hthree, vectorRepresentation_det_r]
  have hunit : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val = 1 := by
    simp [inv_pow, Complex.exp_ne_zero]
  simp only [map_add, map_one]
  have hpoly := congrArg Polynomial.C hunit
  rw [map_mul, map_one] at hpoly
  linear_combination -Polynomial.X ^ 2 * hpoly

/-- The full right trace has the exact determinant numerator at every element. -/
theorem rightTrace_determinant (element : DihedralGroup n) :
    (vectorDenominator n element : PowerSeries ℂ) * rightTrace n hthree element =
      (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ n) := by
  cases element with
  | sr coordinate =>
      rw [vectorDenominator_sr, rightTrace_sr]
      simp
  | r coordinate =>
      rw [vector_factor n hthree, rightTrace_r]
      let root := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
      have hroot : root ^ n = 1 := (isPrimitiveRoot_exp_rotation_angle n).pow_eq_one
      have hunit : root⁻¹ ^ coordinate.val * root ^ coordinate.val = 1 := by
        simp [root, inv_pow, Complex.exp_ne_zero]
      have hsecond : (root ^ coordinate.val) ^ n = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
      have hfirst : (root⁻¹ ^ coordinate.val) ^ n = 1 := by
        rw [inv_pow, inv_pow, hsecond, inv_one]
      have h := Schubert.Splines.paired_trace_identity n
        (root⁻¹ ^ coordinate.val) (root ^ coordinate.val) hunit hfirst hsecond
      let morphism : Polynomial ℂ →+* PowerSeries ℂ := Polynomial.coeToPowerSeries.ringHom
      have hm := congrArg morphism h
      simp only [map_mul, map_add, map_sub, map_pow, map_one, map_sum] at hm
      simpa [morphism, root, inv_pow, PowerSeries.C_inv, ← map_pow] using hm

/-- The full right trace is the paper determinant quotient in formal series. -/
theorem rightTrace_formula (element : DihedralGroup n) :
    rightTrace n hthree element = (1 - PowerSeries.X ^ 2) * (1 - PowerSeries.X ^ n) *
      (vectorDenominator n element : PowerSeries ℂ)⁻¹ := by
  have hconstant : PowerSeries.constantCoeff
      (vectorDenominator n element : PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, vectorDenominator_constant]
    exact one_ne_zero
  apply (PowerSeries.eq_mul_inv_iff_mul_eq hconstant).mpr
  simpa only [mul_comm] using rightTrace_determinant n hthree element

/-- The identity trace is the exact full coinvariant geometric Hilbert numerator. -/
theorem rightTrace_one :
    rightTrace n hthree 1 = (1 + PowerSeries.X) *
      ∑ degree ∈ Finset.range n, (PowerSeries.X : PowerSeries ℂ) ^ degree := by
  change rightTrace n hthree (.r 0) = _
  rw [rightTrace_r]
  simp only [ZMod.val_zero, pow_zero, map_one, one_mul]
  have h := mul_neg_geom_sum (PowerSeries.X : PowerSeries ℂ) n
  linear_combination h

/-- The polynomial degree-one action is the defining plane representation. -/
theorem polynomial_one_iso :
    Nonempty (polynomialPieceFDRep n 1 ≅ FDRep.of (vectorRepresentation n)) := by
  apply FDRep.nonempty_iso_of_character_eq
  calc
    (polynomialPieceFDRep n 1).character = (frequencyFDRep n (1 : ZMod n)).character := by
      have h := FDRep.char_iso (polynomialPiece_odd_iso n 0).some
      rw [Schubert.FiniteGroupCharacters.finiteSum_character] at h
      funext element
      simpa using congrFun h element
    _ = _ := FDRep.char_iso (frequency_one_iso n).some

end Schubert.DihedralSplines.SchubertSpline
