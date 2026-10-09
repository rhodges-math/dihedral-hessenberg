import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
import DihedralHessenberg.Dihedral.PolynomialAction
import DihedralHessenberg.Dihedral.RootGeometry

/-!
# Distinct positive-root linear polynomials

The vector-to-polynomial map is injective. Positive dihedral roots have distinct complex
lines, so their associated linear polynomials are nonzero and pairwise nonassociate.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The polynomial associated to a vector determines both coordinates of that vector. -/
theorem linearPolynomial_injective : Function.Injective linearPolynomial := by
  intro first second heq
  apply complexPlane_ext
  · have heval := congrArg (MvPolynomial.eval (coordinateBasisVector 0)) heq
    simpa [linearPolynomial_eval, complexBilinearForm, coordinateBasisVector] using heval
  · have heval := congrArg (MvPolynomial.eval (coordinateBasisVector 1)) heq
    simpa [linearPolynomial_eval, complexBilinearForm, coordinateBasisVector] using heval

theorem linearPolynomial_zero : linearPolynomial (0 : ComplexPlane) = 0 := by
  simp [linearPolynomial]

theorem linearPolynomial_sub (first second : ComplexPlane) :
    linearPolynomial (first - second) = linearPolynomial first - linearPolynomial second := by
  simp only [linearPolynomial, Pi.sub_apply, map_sub]
  ring

theorem complexBilinearForm_basis (normal : ComplexPlane) (coordinate : Fin 2) :
    complexBilinearForm (coordinateBasisVector coordinate) normal = normal coordinate := by
  fin_cases coordinate <;> simp [coordinateBasisVector, complexBilinearForm]

/-- The difference of a variable and its reflected image is a scalar multiple of the normal form. -/
theorem reflection_variable_difference (normal : ComplexPlane) (coordinate : Fin 2) :
    MvPolynomial.X coordinate -
        polynomialSubstitution (complexReflection normal) (MvPolynomial.X coordinate) =
      MvPolynomial.C (2 * normal coordinate / complexBilinearForm normal normal) *
        linearPolynomial normal := by
  rw [polynomialSubstitution_variable, complexReflection_apply, linearPolynomial_sub,
    linearPolynomial_smul, linearPolynomial_basis, complexBilinearForm_basis]
  ring

/-- Reflection negates the polynomial associated to its nonisotropic normal. -/
theorem reflection_normal_polynomial (normal : ComplexPlane)
    (hnormal : complexBilinearForm normal normal ≠ 0) :
    polynomialSubstitution (complexReflection normal) (linearPolynomial normal) =
      -linearPolynomial normal := by
  rw [polynomialSubstitution_linearPolynomial, complexReflection_normal normal hnormal]
  simp only [linearPolynomial, Pi.neg_apply, map_neg]
  ring

/-- The polynomial of a nonzero vector is nonzero. -/
theorem linearPolynomial_ne_zero (vector : ComplexPlane) (hvector : vector ≠ 0) :
    linearPolynomial vector ≠ 0 := by
  intro hzero
  apply hvector
  apply linearPolynomial_injective
  simpa only [linearPolynomial_zero] using hzero

/-- The complexified positive roots are nonzero. -/
theorem complexPositiveRoot_ne_zero (n : ℕ) (index : PositiveRootIndex n) :
    complexPositiveRoot n index ≠ 0 := by
  intro hzero
  have hunit := complexPositiveRoot_unit n index
  rw [hzero] at hunit
  simp [complexBilinearForm] at hunit

/-- Positive roots which are proportional over the complex numbers have the same index. -/
theorem complexPositiveRoot_smul_eq_imp_index_eq (n : ℕ)
    (first second : PositiveRootIndex n) (scalar : ℂ)
    (heq : complexPositiveRoot n first = scalar • complexPositiveRoot n second) :
    first = second := by
  have hzero := congrFun heq 0
  have hone := congrFun heq 1
  change (Real.cos (rootAngle n first) : ℂ) =
    scalar * (Real.cos (rootAngle n second) : ℂ) at hzero
  change (Real.sin (rootAngle n first) : ℂ) =
    scalar * (Real.sin (rootAngle n second) : ℂ) at hone
  have hdeterminant :
      (Real.cos (rootAngle n first) : ℂ) * (Real.sin (rootAngle n second) : ℂ) -
        (Real.sin (rootAngle n first) : ℂ) * (Real.cos (rootAngle n second) : ℂ) = 0 := by
    rw [hzero, hone]
    ring
  have hsine : (Real.sin (rootAngle n second - rootAngle n first) : ℂ) = 0 := by
    simp only [Real.sin_sub, Complex.ofReal_sub, Complex.ofReal_mul]
    linear_combination hdeterminant
  have hsineReal : Real.sin (rootAngle n second - rootAngle n first) = 0 :=
    Complex.ofReal_eq_zero.mp hsine
  have hlower : -Real.pi < rootAngle n second - rootAngle n first := by
    linarith [rootAngle_nonneg n second, rootAngle_lt_pi n first]
  have hupper : rootAngle n second - rootAngle n first < Real.pi := by
    linarith [rootAngle_nonneg n first, rootAngle_lt_pi n second]
  have hangles := (Real.sin_eq_zero_iff_of_lt_of_lt hlower hupper).mp hsineReal
  apply rootAngle_injective n
  linarith

/-- Root polynomials do not vanish. -/
theorem rootPolynomial_ne_zero (n : ℕ) (index : PositiveRootIndex n) :
    rootPolynomial n index ≠ 0 :=
  linearPolynomial_ne_zero _ (complexPositiveRoot_ne_zero n index)

/-- A scalar multiple equality between positive-root polynomials forces equality of indices. -/
theorem rootPolynomial_scalar_mul_imp_index_eq (n : ℕ)
    (first second : PositiveRootIndex n) (scalar : ℂ)
    (heq : rootPolynomial n first = MvPolynomial.C scalar * rootPolynomial n second) :
    first = second := by
  apply complexPositiveRoot_smul_eq_imp_index_eq n first second scalar
  apply linearPolynomial_injective
  simpa only [rootPolynomial, linearPolynomial_smul] using heq

/-- Distinct positive-root polynomials cannot be scalar multiples of one another. -/
theorem rootPolynomial_not_scalar_multiple (n : ℕ) (first second : PositiveRootIndex n)
    (hne : first ≠ second) (scalar : ℂ) :
    rootPolynomial n first ≠ MvPolynomial.C scalar * rootPolynomial n second := by
  intro heq
  exact hne (rootPolynomial_scalar_mul_imp_index_eq n first second scalar heq)

/-- Distinct positive-root polynomials are not associated in the polynomial ring. -/
theorem rootPolynomial_not_associated (n : ℕ) (first second : PositiveRootIndex n)
    (hne : first ≠ second) : ¬ Associated (rootPolynomial n first) (rootPolynomial n second) := by
  rintro ⟨unit, heq⟩
  obtain ⟨scalar, _, hunit⟩ :=
    MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp unit.isUnit
  apply hne
  apply Eq.symm
  apply rootPolynomial_scalar_mul_imp_index_eq n second first scalar
  rw [← heq, hunit, mul_comm]

/-- The polynomial of a nonzero vector has total degree one. -/
theorem linearPolynomial_totalDegree (vector : ComplexPlane) (hvector : vector ≠ 0) :
    (linearPolynomial vector).totalDegree = 1 := by
  have hbound : (linearPolynomial vector).totalDegree ≤ 1 := by
    unfold linearPolynomial
    apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simpa using MvPolynomial.totalDegree_mul
        (MvPolynomial.C (vector 0)) (MvPolynomial.X (0 : Fin 2))
    · simpa using MvPolynomial.totalDegree_mul
        (MvPolynomial.C (vector 1)) (MvPolynomial.X (1 : Fin 2))
  have hnonzero : (linearPolynomial vector).totalDegree ≠ 0 := by
    intro hdegree
    have hconstant := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree
    have hcoefficient : (linearPolynomial vector).coeff 0 = 0 := by
      simp [linearPolynomial]
    rw [hcoefficient, map_zero] at hconstant
    exact linearPolynomial_ne_zero vector hvector hconstant
  omega

/-- Every nonzero linear polynomial arising from a vector is irreducible. -/
theorem linearPolynomial_irreducible (vector : ComplexPlane) (hvector : vector ≠ 0) :
    Irreducible (linearPolynomial vector) := by
  apply MvPolynomial.irreducible_of_totalDegree_eq_one (linearPolynomial_totalDegree vector hvector)
  intro scalar hdivides
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  apply linearPolynomial_ne_zero vector hvector
  ext monomial
  change (linearPolynomial vector).coeff monomial = 0
  simpa only [hzero, zero_dvd_iff] using hdivides monomial

/-- Every positive-root polynomial is irreducible. -/
theorem rootPolynomial_irreducible (n : ℕ) (index : PositiveRootIndex n) :
    Irreducible (rootPolynomial n index) :=
  linearPolynomial_irreducible _ (complexPositiveRoot_ne_zero n index)

/-- Distinct positive-root polynomials have no common nonunit divisor. -/
theorem rootPolynomial_isRelPrime (n : ℕ) (first second : PositiveRootIndex n)
    (hne : first ≠ second) : IsRelPrime (rootPolynomial n first) (rootPolynomial n second) := by
  apply (rootPolynomial_irreducible n first).isRelPrime_iff_not_dvd.mpr
  intro hdivides
  exact rootPolynomial_not_associated n first second hne
    ((rootPolynomial_irreducible n first).associated_of_dvd
      (rootPolynomial_irreducible n second) hdivides)

end Schubert.Dihedral
