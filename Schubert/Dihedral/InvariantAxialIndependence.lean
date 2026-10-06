import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Schubert.Dihedral.InvariantDegrees

/-! # Independence of auxiliary axial pairs over the invariant algebra

A relation between a u-power and a v-power can be reflected. The resulting
pair of equations has a nonzero determinant, which forces both invariant coefficients to vanish.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A nontrivial signed axial difference is nonzero. -/
theorem _root_.Schubert.Dihedral.Axial.signed_pow_difference_ne_zero (first second : ℕ)
    (hpositive : 0 < first + second) :
    MvPolynomial.C ((-1 : ℂ) ^ second) * auxiliaryU ^ (first + second) -
      MvPolynomial.C ((-1 : ℂ) ^ first) * auxiliaryV ^ (first + second) ≠ 0 := by
  intro hequal
  have hinverseU : auxiliaryCoordinateEquiv.symm auxiliaryU = MvPolynomial.X 0 := by
    rw [← auxiliaryCoordinateEquiv_X_zero, AlgEquiv.symm_apply_apply]
  have hinverseV : auxiliaryCoordinateEquiv.symm auxiliaryV = MvPolynomial.X 1 := by
    rw [← auxiliaryCoordinateEquiv_X_one, AlgEquiv.symm_apply_apply]
  have heval := congrArg
    (fun polynomial => MvPolynomial.eval ![(1 : ℂ), 0]
      (auxiliaryCoordinateEquiv.symm polynomial)) hequal
  simp [hinverseU, hinverseV] at heval
  rw [zero_pow hpositive.ne'] at heval
  simp at heval

/-- A relation between an axial pair with invariant coefficients has zero coefficients. -/
theorem invariant_axial_pair_relation (n : ℕ) [NeZero n] (first second : ℕ)
    (hpositive : 0 < first + second) (scalarFirst scalarSecond : invariantSubalgebra n)
    (hrelation : (scalarFirst : CoordinatePolynomial) * auxiliaryU ^ first +
      (scalarSecond : CoordinatePolynomial) * auxiliaryV ^ second = 0) :
    scalarFirst = 0 ∧ scalarSecond = 0 := by
  have hreflected := congrArg (polynomialAction n (firstSimpleReflection n)) hrelation
  have hfixedFirst : polynomialAction n (firstSimpleReflection n)
      (scalarFirst : CoordinatePolynomial) = scalarFirst :=
    (mem_invariantSubalgebra n _).mp scalarFirst.property _
  have hfixedSecond : polynomialAction n (firstSimpleReflection n)
      (scalarSecond : CoordinatePolynomial) = scalarSecond :=
    (mem_invariantSubalgebra n _).mp scalarSecond.property _
  simp only [map_add, map_mul, map_pow, map_zero, hfixedFirst, hfixedSecond,
    polynomialAction_firstSimple_auxiliaryU, polynomialAction_firstSimple_auxiliaryV,
    neg_pow auxiliaryV first, neg_pow auxiliaryU second] at hreflected
  have hproduct : (scalarFirst : CoordinatePolynomial) *
      (MvPolynomial.C ((-1 : ℂ) ^ second) * auxiliaryU ^ (first + second) -
        MvPolynomial.C ((-1 : ℂ) ^ first) * auxiliaryV ^ (first + second)) = 0 := by
    rw [pow_add, pow_add]
    have hsignFirst : (MvPolynomial.C ((-1 : ℂ) ^ first) : CoordinatePolynomial) =
        (-1) ^ first := by simp
    have hsignSecond : (MvPolynomial.C ((-1 : ℂ) ^ second) : CoordinatePolynomial) =
        (-1) ^ second := by simp
    rw [hsignFirst, hsignSecond]
    linear_combination (-1 : CoordinatePolynomial) ^ second * auxiliaryU ^ second * hrelation -
      auxiliaryV ^ second * hreflected
  have hfirst : (scalarFirst : CoordinatePolynomial) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_right
      (_root_.Schubert.Dihedral.Axial.signed_pow_difference_ne_zero first second hpositive)
  have hsecond : (scalarSecond : CoordinatePolynomial) = 0 := by
    rw [hfirst, zero_mul, zero_add] at hrelation
    exact (mul_eq_zero.mp hrelation).resolve_right (pow_ne_zero _ auxiliaryV_ne_zero)
  exact ⟨Subtype.ext hfirst, Subtype.ext hsecond⟩

/-- Every nonconstant axial pair is linearly independent over the invariant algebra. -/
theorem invariant_axial_pair_linearIndependent (n : ℕ) [NeZero n] (first second : ℕ)
    (hpositive : 0 < first + second) :
    LinearIndependent (invariantSubalgebra n) ![auxiliaryU ^ first, auxiliaryV ^ second] := by
  apply LinearIndependent.pair_iff.mpr
  intro scalarFirst scalarSecond hrelation
  exact invariant_axial_pair_relation n first second hpositive scalarFirst scalarSecond hrelation

end Schubert.Dihedral
