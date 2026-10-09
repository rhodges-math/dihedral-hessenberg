import Mathlib.RingTheory.RootsOfUnity.Complex
import DihedralHessenberg.Dihedral.Invariants

/-! # Basic invariant and coinvariant polynomial facts

Linear substitution preserves augmentation. The positive invariant ideal is stable under
the group action and is contained in the augmentation ideal. Auxiliary monomials have
explicit rotation eigenvalues and reflection images.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Linear polynomial substitution preserves the constant coefficient. -/
theorem polynomialSubstitution_constantCoeff (operator : ComplexPlane →ₗ[ℂ] ComplexPlane)
    (polynomial : CoordinatePolynomial) :
    (polynomialSubstitution operator polynomial).constantCoeff = polynomial.constantCoeff := by
  induction polynomial using MvPolynomial.induction_on with
  | C scalar => simp [polynomialSubstitution]
  | add first second hfirst hsecond => simp [hfirst, hsecond]
  | mul_X polynomial coordinate hpolynomial =>
    rw [map_mul, polynomialSubstitution_variable]
    simp [linearPolynomial]

/-- The dihedral action preserves the polynomial augmentation. -/
theorem polynomialAction_constantCoeff (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    (polynomialAction n element polynomial).constantCoeff = polynomial.constantCoeff := by
  rw [polynomialAction_apply]
  exact polynomialSubstitution_constantCoeff _ _

/-- The image of the positive invariant generating set under any group element is itself. -/
theorem _root_.Schubert.Dihedral.Invariants.action_positive (n : ℕ) [NeZero n]
    (element : DihedralGroup n) :
    polynomialAction n element '' positiveInvariantPolynomials n =
      positiveInvariantPolynomials n := by
  ext polynomial
  constructor
  · rintro ⟨preimage, hpreimage, heq⟩
    have hfixed := (mem_invariantSubalgebra n preimage).mp hpreimage.1 element
    rw [hfixed] at heq
    exact heq ▸ hpreimage
  · intro hpolynomial
    exact ⟨polynomial, hpolynomial,
      (mem_invariantSubalgebra n polynomial).mp hpolynomial.1 element⟩

/-- The coinvariant ideal is preserved by the dihedral polynomial action. -/
theorem polynomialAction_map_coinvariantIdeal (n : ℕ) [NeZero n]
    (element : DihedralGroup n) :
    Ideal.map (polynomialAction n element).toRingHom (coinvariantIdeal n) = coinvariantIdeal n := by
  rw [coinvariantIdeal, Ideal.map_span]
  exact congrArg Ideal.span (_root_.Schubert.Dihedral.Invariants.action_positive n element)

/-- The coinvariant ideal is contained in the augmentation ideal. -/
theorem coinvariantIdeal_le_augmentation (n : ℕ) [NeZero n] :
    coinvariantIdeal n ≤ RingHom.ker
      (MvPolynomial.constantCoeff : CoordinatePolynomial →+* ℂ) := by
  rw [coinvariantIdeal, Ideal.span_le]
  intro polynomial hpolynomial
  exact hpolynomial.2

/-- The coinvariant ideal is proper. -/
theorem coinvariantIdeal_ne_top (n : ℕ) [NeZero n] : coinvariantIdeal n ≠ ⊤ := by
  intro htop
  have hone : (1 : CoordinatePolynomial) ∈ coinvariantIdeal n := by rw [htop]; trivial
  have hzero := coinvariantIdeal_le_augmentation n hone
  change MvPolynomial.constantCoeff (1 : CoordinatePolynomial) = 0 at hzero
  simp at hzero

/-- The positive fundamental rotation eigenvalue is a primitive nth root of unity. -/
theorem isPrimitiveRoot_rotationEigenvalue (n : ℕ) [NeZero n] :
    IsPrimitiveRoot (Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I)) n := by
  convert Complex.isPrimitiveRoot_exp n (NeZero.ne n) using 1
  congr 1
  push_cast
  ring

/-- An auxiliary monomial is an eigenvector for arbitrary coordinate rotations. -/
theorem _root_.Schubert.Dihedral.Axial.subst_rotation_monomial (angle : ℝ) (first second : ℕ) :
    polynomialSubstitution (complexRotation angle) (auxiliaryU ^ first * auxiliaryV ^ second) =
      MvPolynomial.C (Complex.exp (((-angle : ℝ) : ℂ) * Complex.I) ^ first *
        Complex.exp ((angle : ℂ) * Complex.I) ^ second) *
        (auxiliaryU ^ first * auxiliaryV ^ second) := by
  rw [map_mul, map_pow, map_pow, _root_.Schubert.Dihedral.Axial.subst_rotation_u_exp,
    _root_.Schubert.Dihedral.Axial.subst_rotation_v_exp]
  simp only [mul_pow]
  rw [map_mul, map_pow, map_pow]
  ring

/-- Coordinate reflection interchanges auxiliary monomial exponents with the parity sign. -/
theorem _root_.Schubert.Dihedral.Axial.subst_reflection_monomial (first second : ℕ) :
    polynomialSubstitution (complexReflection (complexify (unitRootAt 0)))
        (auxiliaryU ^ first * auxiliaryV ^ second) =
      MvPolynomial.C ((-1 : ℂ) ^ (first + second)) *
        (auxiliaryU ^ second * auxiliaryV ^ first) := by
  rw [map_mul, map_pow, map_pow, _root_.Schubert.Dihedral.Axial.subst_reflection_u,
    _root_.Schubert.Dihedral.Axial.subst_reflection_v]
  rw [neg_pow auxiliaryV first, neg_pow auxiliaryU second]
  rw [pow_add]
  simp only [map_mul, map_pow, map_neg, map_one]
  ring

end Schubert.Dihedral
