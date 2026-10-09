import DihedralHessenberg.Splines.HomogeneousDivisibility

/-! # Homogeneous components and exact division by homogeneous polynomials -/

namespace Schubert.Splines

variable {K P : Type*} [CommRing K]

/-- Multiplication by a homogeneous polynomial shifts each homogeneous component. -/
theorem homogeneousComponent_mul_of_homogeneous
    {factor : MvPolynomial P K} {factorDegree : ℕ}
    (hfactor : factor.IsHomogeneous factorDegree) (value : MvPolynomial P K) (degree : ℕ) :
    MvPolynomial.homogeneousComponent (factorDegree + degree) (factor * value) =
      factor * MvPolynomial.homogeneousComponent degree value := by
  classical
  have hcomponent (index : ℕ) :
      MvPolynomial.homogeneousComponent (factorDegree + degree)
          (factor * MvPolynomial.homogeneousComponent index value) =
        if index = degree then factor * MvPolynomial.homogeneousComponent degree value else 0 := by
    have hhomogeneous := hfactor.mul
      (MvPolynomial.homogeneousComponent_isHomogeneous index value)
    rw [MvPolynomial.homogeneousComponent_of_mem hhomogeneous]
    by_cases heq : index = degree
    · subst index
      simp
    · simp [heq, Ne.symm heq, Nat.add_left_cancel_iff]
  calc
    _ = MvPolynomial.homogeneousComponent (factorDegree + degree)
        (factor * ∑ index ∈ Finset.range (value.totalDegree + 1),
          MvPolynomial.homogeneousComponent index value) := by
      rw [MvPolynomial.sum_homogeneousComponent]
    _ = ∑ index ∈ Finset.range (value.totalDegree + 1),
        (if index = degree then
          factor * MvPolynomial.homogeneousComponent degree value else 0) := by
      simp only [Finset.mul_sum, map_sum, hcomponent]
    _ = factor * MvPolynomial.homogeneousComponent degree value := by
      rw [Finset.sum_eq_single degree]
      · simp
      · intro index _ hne
        simp [hne]
      · intro hnot
        have hbound : value.totalDegree < degree := by
          simp only [Finset.mem_range] at hnot
          omega
        simp [MvPolynomial.homogeneousComponent_eq_zero degree value hbound]

/-- Exact division by a nonzero homogeneous factor leaves the expected homogeneous degree. -/
theorem polynomial_quotient_isHomogeneous [IsDomain K]
    {factor quotient : MvPolynomial P K} {factorDegree degree : ℕ}
    (hfactor : factor.IsHomogeneous factorDegree) (hnonzero : factor ≠ 0)
    (hproduct : (factor * quotient).IsHomogeneous (factorDegree + degree)) :
    quotient.IsHomogeneous degree := by
  have hprojection := homogeneousComponent_mul_of_homogeneous hfactor quotient degree
  rw [MvPolynomial.homogeneousComponent_eq_self hproduct] at hprojection
  have heq := mul_left_cancel₀ hnonzero hprojection
  rw [heq]
  exact MvPolynomial.homogeneousComponent_isHomogeneous degree quotient

end Schubert.Splines
