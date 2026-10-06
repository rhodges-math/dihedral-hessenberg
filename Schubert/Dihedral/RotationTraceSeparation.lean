import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Schubert.Dihedral.InvariantRotationSeparation

/-! # Separation of sums of inverse rotation eigenvalues

The quadratic trace expression separates frequencies in the lower half of a period.
This is a scalar calculation independent of any representation bundling.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Two nonzero scalars have the same inverse sum exactly when equal or inverse. -/
theorem add_inverse_eq_iff {K : Type*} [Field K] (first second : K)
    (hfirst : first ≠ 0) (hsecond : second ≠ 0) :
    first + first⁻¹ = second + second⁻¹ ↔ first = second ∨ first = second⁻¹ := by
  constructor
  · intro hequal
    have hfactor : (first - second) * (first * second - 1) = 0 := by
      field_simp [hfirst, hsecond] at hequal
      linear_combination hequal
    rcases mul_eq_zero.mp hfactor with hdifference | hproduct
    · exact Or.inl (sub_eq_zero.mp hdifference)
    · right
      apply mul_right_cancel₀ hsecond
      rw [inv_mul_cancel₀ hsecond]
      exact sub_eq_zero.mp hproduct
  · rintro (rfl | rfl)
    · rfl
    · simp [add_comm]

/-- Rotation inverse sums distinguish frequencies strictly below half the rotation order. -/
theorem rotationEigenvalue_inverse_sum_eq_iff (n : ℕ) [NeZero n] (first second : ℕ)
    (hfirst : 2 * first < n) (hsecond : 2 * second < n) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ first +
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ first)⁻¹ =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ second +
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ second)⁻¹ ↔
      first = second := by
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hnonzero : eigenvalue ≠ 0 := Complex.exp_ne_zero _
  have hprimitive : IsPrimitiveRoot eigenvalue n := isPrimitiveRoot_exp_rotation_angle n
  change eigenvalue ^ first + (eigenvalue ^ first)⁻¹ =
    eigenvalue ^ second + (eigenvalue ^ second)⁻¹ ↔ _
  rw [add_inverse_eq_iff _ _ (pow_ne_zero _ hnonzero) (pow_ne_zero _ hnonzero)]
  constructor
  · rintro (hequal | hinverse)
    · exact hprimitive.pow_inj (by omega) (by omega) hequal
    · have hpower : eigenvalue ^ (first + second) = 1 := by
        rw [pow_add, hinverse, inv_mul_cancel₀ (pow_ne_zero _ hnonzero)]
      have hdivisible := (hprimitive.pow_eq_one_iff_dvd _).mp hpower
      have hzero := Nat.eq_zero_of_dvd_of_lt hdivisible (show first + second < n by omega)
      omega
  · intro hequal
    exact Or.inl (congrArg (fun frequency => eigenvalue ^ frequency) hequal)

/-- A positive frequency below half the period has inverse sum different from two. -/
theorem rotationEigenvalue_inverse_sum_ne_two (n : ℕ) [NeZero n] (frequency : ℕ)
    (hpositive : 0 < frequency) (hbelow : 2 * frequency < n) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency +
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency)⁻¹ ≠ 2 := by
  intro hequal
  have hzero : frequency = 0 :=
    (rotationEigenvalue_inverse_sum_eq_iff n frequency 0 hbelow (by omega)).mp
      (by norm_num at *; exact hequal)
  omega

/-- A positive frequency below half the period has inverse sum different from minus two. -/
theorem _root_.Schubert.Dihedral.RotationTrace.ne_neg_two (n : ℕ) [NeZero n] (frequency : ℕ)
    (hpositive : 0 < frequency) (hbelow : 2 * frequency < n) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency +
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency)⁻¹ ≠ -2 := by
  intro hequal
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hnonzero : eigenvalue ≠ 0 := Complex.exp_ne_zero _
  have hprimitive : IsPrimitiveRoot eigenvalue n := isPrimitiveRoot_exp_rotation_angle n
  have hsame : eigenvalue ^ frequency + (eigenvalue ^ frequency)⁻¹ =
      (-1 : ℂ) + (-1 : ℂ)⁻¹ := by norm_num [eigenvalue] at *; exact hequal
  have hminus : eigenvalue ^ frequency = -1 := by
    simpa using (add_inverse_eq_iff _ _ (pow_ne_zero _ hnonzero)
      (neg_ne_zero.mpr one_ne_zero)).mp hsame
  have hpower : eigenvalue ^ (2 * frequency) = 1 := by
    rw [two_mul, pow_add, hminus]
    norm_num
  have hdivisible := (hprimitive.pow_eq_one_iff_dvd _).mp hpower
  have hzero := Nat.eq_zero_of_dvd_of_lt hdivisible hbelow
  omega
end Schubert.Dihedral



