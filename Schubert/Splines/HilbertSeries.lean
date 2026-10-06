import Mathlib.RingTheory.PowerSeries.WellKnown

/-! # The two-variable homogeneous Hilbert kernel -/

namespace Schubert.Splines.Hilbert

/-- The standard inverse-square geometric series has coefficient d+1 in degree d. -/
theorem kernel_coeff (degree : ℕ) :
    PowerSeries.coeff degree (PowerSeries.invOneSubPow ℚ 2).val = (degree + 1 : ℚ) := by
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk]
  simp [add_comm]

/-- The inverse-square geometric kernel cancels the displayed quadratic denominator. -/
theorem kernel_mul_denominator :
    (PowerSeries.invOneSubPow ℚ 2).val * (1 - PowerSeries.X) ^ 2 = 1 :=
  (PowerSeries.invOneSubPow ℚ 2).val_inv

/-- Multiplying the geometric kernel by a degree shift gives the expected truncated coefficient. -/
theorem shifted_kernel_coeff (shift degree : ℕ) :
    PowerSeries.coeff degree
      ((PowerSeries.X : PowerSeries ℚ) ^ shift * (PowerSeries.invOneSubPow ℚ 2).val) =
      if shift ≤ degree then ((degree - shift + 1 : ℕ) : ℚ) else 0 := by
  rw [mul_comm, PowerSeries.coeff_mul_X_pow']
  split_ifs with hle
  · rw [kernel_coeff]
    norm_cast
  · rfl

/-- A finite degree polynomial times the kernel has the exact degree convolution coefficients. -/
theorem finite_coeff {I : Type*} [Fintype I] (degrees : I → ℕ) (degree : ℕ) :
    PowerSeries.coeff degree
      ((∑ index, (PowerSeries.X : PowerSeries ℚ) ^ degrees index) *
        (PowerSeries.invOneSubPow ℚ 2).val) =
      ∑ index, if degrees index ≤ degree then ((degree - degrees index + 1 : ℕ) : ℚ) else 0 := by
  rw [Finset.sum_mul]
  simp only [map_sum, shifted_kernel_coeff]

/-- The full formal series with convolution coefficients factors by the quadratic Hilbert kernel.
-/
theorem finite_series {I : Type*} [Fintype I] (degrees : I → ℕ) :
    PowerSeries.mk (fun degree => ∑ index,
      if degrees index ≤ degree then ((degree - degrees index + 1 : ℕ) : ℚ) else 0) =
      (∑ index, (PowerSeries.X : PowerSeries ℚ) ^ degrees index) *
        (PowerSeries.invOneSubPow ℚ 2).val := by
  ext degree
  rw [PowerSeries.coeff_mk, finite_coeff]

/-- Multiplying the complete convolution series by its denominator gives the degree polynomial. -/
theorem finite_denominator {I : Type*} [Fintype I] (degrees : I → ℕ) :
    PowerSeries.mk (fun degree => ∑ index,
      if degrees index ≤ degree then ((degree - degrees index + 1 : ℕ) : ℚ) else 0) *
      (1 - PowerSeries.X) ^ 2 =
      ∑ index, (PowerSeries.X : PowerSeries ℚ) ^ degrees index := by
  rw [finite_series, mul_assoc, kernel_mul_denominator, mul_one]

end Schubert.Splines.Hilbert
