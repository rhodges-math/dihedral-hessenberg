import Mathlib.Algebra.Field.GeomSum
import Schubert.Dihedral.InvariantCoefficients

/-! # Finite Fourier sums of the primitive rotation eigenvalue

Summing a rotation frequency over one full period gives zero unless the frequency
is divisible by the group order. This is independent of representation bundling.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A full-period sum of a primitive rotation frequency detects divisibility by the order. -/
theorem rotationEigenvalue_frequency_sum (n : ℕ) [NeZero n] (frequency : ℕ) :
    (∑ exponent ∈ Finset.range n,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency) ^ exponent) =
      if n ∣ frequency then (n : ℂ) else 0 := by
  classical
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hprimitive : IsPrimitiveRoot eigenvalue n := isPrimitiveRoot_exp_rotation_angle n
  change (∑ exponent ∈ Finset.range n, (eigenvalue ^ frequency) ^ exponent) = _
  by_cases hdivisible : n ∣ frequency
  · have hone : eigenvalue ^ frequency = 1 :=
      (hprimitive.pow_eq_one_iff_dvd frequency).mpr hdivisible
    simp [hdivisible, hone]
  · have hne : eigenvalue ^ frequency ≠ 1 :=
      fun hequal => hdivisible ((hprimitive.pow_eq_one_iff_dvd frequency).mp hequal)
    have hpower : (eigenvalue ^ frequency) ^ n = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hprimitive.pow_eq_one, one_pow]
    rw [ite_eq_right hdivisible, geom_sum_eq hne]
    simp [hpower]

/-- The same frequency sum expressed using the finite rotation index type. -/
theorem rotationEigenvalue_frequency_sum_fin (n : ℕ) [NeZero n] (frequency : ℕ) :
    (∑ exponent : Fin n,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ frequency) ^ exponent.val) =
      if n ∣ frequency then (n : ℂ) else 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact rotationEigenvalue_frequency_sum n frequency

/-- Distinct indexed rotation eigenvalues are orthogonal over a complete period. -/
theorem rotationEigenvalue_ratio_sum (n : ℕ) [NeZero n] (first second : Fin n) :
    (∑ exponent : Fin n,
      (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ first.val /
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ second.val) ^ exponent.val) =
      if first = second then (n : ℂ) else 0 := by
  classical
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hprimitive : IsPrimitiveRoot eigenvalue n := isPrimitiveRoot_exp_rotation_angle n
  have hnonzero : eigenvalue ^ second.val ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  change (∑ exponent : Fin n,
    (eigenvalue ^ first.val / eigenvalue ^ second.val) ^ exponent.val) = _
  by_cases hequal : first = second
  · subst second
    simp [hnonzero]
  · have hne : eigenvalue ^ first.val / eigenvalue ^ second.val ≠ 1 := by
      intro hone
      exact hequal (Fin.ext (hprimitive.pow_inj first.isLt second.isLt
        ((div_eq_one_iff_eq hnonzero).mp hone)))
    have hpower : (eigenvalue ^ first.val / eigenvalue ^ second.val) ^ n = 1 := by
      rw [div_pow]
      have hfirst : (eigenvalue ^ first.val) ^ n = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hprimitive.pow_eq_one, one_pow]
      have hsecond : (eigenvalue ^ second.val) ^ n = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hprimitive.pow_eq_one, one_pow]
      rw [hfirst, hsecond, div_self one_ne_zero]
    rw [ite_eq_right hequal, Fin.sum_univ_eq_sum_range, geom_sum_eq hne]
    simp [hpower]

end Schubert.Dihedral
