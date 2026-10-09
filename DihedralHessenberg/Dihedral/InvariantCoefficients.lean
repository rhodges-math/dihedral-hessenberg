import DihedralHessenberg.Dihedral.AuxiliaryAction
import DihedralHessenberg.Dihedral.DiagonalCoefficients
import DihedralHessenberg.Dihedral.InvariantsBasic

/-! # Rotation constraints on invariant coefficients

Expressing an invariant in the auxiliary coordinates restricts its nonzero monomials
to exponents whose difference is divisible by the rotation order.
-/

noncomputable section

namespace Schubert.Dihedral

/-- An invariant in auxiliary coordinates is fixed by the diagonal fundamental rotation. -/
theorem invariant_auxiliary_diagonal_fixed (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) (hinvariant : polynomial ∈ invariantSubalgebra n) :
    MvPolynomial.aeval (fun coordinate : Fin 2 => if coordinate = 0 then
        MvPolynomial.C ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹) *
          MvPolynomial.X (0 : Fin 2)
        else MvPolynomial.C (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) *
          MvPolynomial.X (1 : Fin 2)) (auxiliaryCoordinateEquiv.symm polynomial) =
      auxiliaryCoordinateEquiv.symm polynomial := by
  apply auxiliaryCoordinateEquiv.injective
  rw [← _root_.Schubert.Dihedral.AuxiliaryAction.action_rotation_axialEquiv n hthree,
    auxiliaryCoordinateEquiv.apply_symm_apply]
  exact (mem_invariantSubalgebra n polynomial).mp hinvariant (rotation n)

/-- Nonzero auxiliary coefficients of an invariant have equal rotation eigenvalue powers. -/
theorem invariant_auxiliary_coefficient_pow_eq (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) (hinvariant : polynomial ∈ invariantSubalgebra n)
    (exponent : Fin 2 →₀ ℕ)
    (hnonzero : (auxiliaryCoordinateEquiv.symm polynomial).coeff exponent ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent 0 =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent 1 := by
  have heigen := diagonal_eigenvalue_eq_one_of_fixed _ _
    (auxiliaryCoordinateEquiv.symm polynomial) exponent
    (invariant_auxiliary_diagonal_fixed n hthree polynomial hinvariant) hnonzero
  have hnonzeroPower : Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ exponent 0 ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  rw [inv_pow, mul_comm, ← div_eq_mul_inv] at heigen
  exact ((div_eq_one_iff_eq hnonzeroPower).mp heigen).symm

/-- The primitive positive rotation eigenvalue has the explicit complex-angle formula. -/
theorem isPrimitiveRoot_exp_rotation_angle (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)) n := by
  convert isPrimitiveRoot_rotationEigenvalue n using 1
  congr 1
  push_cast
  ring

/-- When the second exponent is larger, its excess is divisible by n. -/
theorem invariant_auxiliary_coefficient_dvd_sub (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) (hinvariant : polynomial ∈ invariantSubalgebra n)
    (exponent : Fin 2 →₀ ℕ)
    (hnonzero : (auxiliaryCoordinateEquiv.symm polynomial).coeff exponent ≠ 0)
    (horder : exponent 0 ≤ exponent 1) : n ∣ exponent 1 - exponent 0 := by
  apply ((isPrimitiveRoot_exp_rotation_angle n).pow_eq_one_iff_dvd _).mp
  rw [pow_sub₀ _ (Complex.exp_ne_zero _) horder,
    ← invariant_auxiliary_coefficient_pow_eq n hthree polynomial hinvariant exponent hnonzero]
  exact mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))

/-- When the first exponent is larger, its excess is divisible by n. -/
theorem _root_.Schubert.Dihedral.Invariants.coefficient_dvd_sub_reverse (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) (polynomial : CoordinatePolynomial)
    (hinvariant : polynomial ∈ invariantSubalgebra n) (exponent : Fin 2 →₀ ℕ)
    (hnonzero : (auxiliaryCoordinateEquiv.symm polynomial).coeff exponent ≠ 0)
    (horder : exponent 1 ≤ exponent 0) : n ∣ exponent 0 - exponent 1 := by
  apply ((isPrimitiveRoot_exp_rotation_angle n).pow_eq_one_iff_dvd _).mp
  rw [pow_sub₀ _ (Complex.exp_ne_zero _) horder,
    invariant_auxiliary_coefficient_pow_eq n hthree polynomial hinvariant exponent hnonzero]
  exact mul_inv_cancel₀ (pow_ne_zero _ (Complex.exp_ne_zero _))

end Schubert.Dihedral
