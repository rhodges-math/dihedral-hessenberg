import Lean.Elab.Tactic.Omega
import DihedralHessenberg.Dihedral.AuxiliaryCoordinates

/-! # Fundamental rotation eigenvalues

For r = s1*s2 and zeta = exp(2*pi*i/n), the polynomial column-substitution convention
acts on u by zeta inverse and on v by zeta.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The fundamental rotation acts on u with the inverse primitive rotation eigenvalue. -/
theorem polynomialAction_rotation_auxiliaryU (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    polynomialAction n (rotation n) auxiliaryU =
      MvPolynomial.C ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹) * auxiliaryU := by
  have hvalue : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  rw [rotation_eq_r_one, polynomialAction_r_auxiliaryU, hvalue, Nat.cast_one, mul_one]
  have hangle : (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I / n := by
    push_cast
    ring
  rw [Complex.ofReal_neg, neg_mul, Complex.exp_neg, hangle]

/-- The fundamental rotation acts on v with the primitive positive rotation eigenvalue. -/
theorem polynomialAction_rotation_auxiliaryV (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    polynomialAction n (rotation n) auxiliaryV =
      MvPolynomial.C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) * auxiliaryV := by
  have hvalue : (1 : ZMod n).val = 1 := ZMod.val_one'' (by omega)
  rw [rotation_eq_r_one, polynomialAction_r_auxiliaryV, hvalue, Nat.cast_one, mul_one]
  have hangle : (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I / n := by
    push_cast
    ring
  rw [hangle]

end Schubert.Dihedral
