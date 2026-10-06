import Schubert.Splines.HomogeneousDivisibility

/-! # Homogeneity of minimal-degree label multiples

A nonzero polynomial divisible by a homogeneous product cannot have smaller degree.
If its degree is bounded by that product degree, its remaining factor is constant.
-/

namespace Schubert.Splines

variable {K P : Type*} [Field K]

/-- A nonzero multiple of a homogeneous polynomial with no larger degree is homogeneous. -/
theorem _root_.Schubert.Splines.HomogeneousMultiple.of_dvd_degree_le
    {divisor multiple : MvPolynomial P K} {degree : ℕ}
    (hdivisor : divisor.IsHomogeneous degree) (hdivides : divisor ∣ multiple)
    (hnonzero : multiple ≠ 0) (hdegree : multiple.totalDegree ≤ degree) :
    multiple.IsHomogeneous degree := by
  obtain ⟨factor, rfl⟩ := hdivides
  have hdivisorNonzero : divisor ≠ 0 := left_ne_zero_of_mul hnonzero
  have hfactorNonzero : factor ≠ 0 := right_ne_zero_of_mul hnonzero
  rw [MvPolynomial.totalDegree_mul_of_isDomain hdivisorNonzero hfactorNonzero,
    hdivisor.totalDegree hdivisorNonzero] at hdegree
  have hfactorDegree : factor.totalDegree = 0 := by omega
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hfactorDegree]
  simpa only [mul_comm] using hdivisor.C_mul (factor.coeff 0)

end Schubert.Splines
