import DihedralHessenberg.Dihedral.InvariantRotationSeparation

/-! # Separation of inverse rotation eigenvalues

The inverse and positive frequency eigenvalues coincide exactly at frequencies whose
double is divisible by the dihedral rotation order.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Inverse and positive eigenvalue powers agree exactly at the exceptional doubled frequencies. -/
theorem rotationEigenvalue_inverse_pow_eq_iff (n : ℕ) [NeZero n] (frequency : ℕ) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency ↔ n ∣ 2 * frequency := by
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hnonzero : eigenvalue ≠ 0 := Complex.exp_ne_zero _
  have hprimitive : IsPrimitiveRoot eigenvalue n := isPrimitiveRoot_exp_rotation_angle n
  change eigenvalue⁻¹ ^ frequency = eigenvalue ^ frequency ↔ _
  constructor
  · intro hequal
    apply (hprimitive.pow_eq_one_iff_dvd _).mp
    calc
      eigenvalue ^ (2 * frequency) = eigenvalue ^ frequency * eigenvalue ^ frequency := by
        rw [two_mul, pow_add]
      _ = eigenvalue ^ frequency * eigenvalue⁻¹ ^ frequency := by rw [hequal]
      _ = 1 := by rw [← mul_pow, mul_inv_cancel₀ hnonzero, one_pow]
  · intro hdivisible
    apply mul_left_cancel₀ (pow_ne_zero frequency hnonzero)
    calc
      eigenvalue ^ frequency * eigenvalue⁻¹ ^ frequency = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hnonzero, one_pow]
      _ = eigenvalue ^ frequency * eigenvalue ^ frequency := by
        rw [← pow_add, ← two_mul, (hprimitive.pow_eq_one_iff_dvd _).mpr hdivisible]

/-- The frequencies strictly between zero and half the rotation order have separated eigenvalues. -/
theorem rotationEigenvalue_inverse_pow_ne (n : ℕ) [NeZero n] (frequency : ℕ)
    (hpositive : 0 < frequency) (hbelow : 2 * frequency < n) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ frequency ≠
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency := by
  intro hequal
  have hdivisible := (rotationEigenvalue_inverse_pow_eq_iff n frequency).mp hequal
  have hzero : 2 * frequency = 0 := Nat.eq_zero_of_dvd_of_lt hdivisible hbelow
  omega

end Schubert.Dihedral
