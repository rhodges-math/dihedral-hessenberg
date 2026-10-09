import DihedralHessenberg.Dihedral.CoinvariantRelations
import DihedralHessenberg.Dihedral.InvariantRotationBlocks

/-! # Polynomial images of coinvariant axial representatives

These formulas describe images of representatives under the existing polynomial
action before passing to the official coinvariant quotient.
-/

noncomputable section

namespace Schubert.Dihedral

/-- A reflected first axial power is the signed second axial class. -/
theorem coinvariant_firstSimple_auxiliaryU_pow (n : ℕ) [NeZero n] (degree : ℕ) :
    Ideal.Quotient.mk (coinvariantIdeal n)
      (polynomialAction n (firstSimpleReflection n) (auxiliaryU ^ degree)) =
      (-1) ^ degree * Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV ^ degree := by
  simp only [map_pow, polynomialAction_firstSimple_auxiliaryU, map_neg]
  exact neg_pow (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryV) degree

/-- A reflected second axial power is the signed first axial class. -/
theorem coinvariant_firstSimple_auxiliaryV_pow (n : ℕ) [NeZero n] (degree : ℕ) :
    Ideal.Quotient.mk (coinvariantIdeal n)
      (polynomialAction n (firstSimpleReflection n) (auxiliaryV ^ degree)) =
      (-1) ^ degree * Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ degree := by
  simp only [map_pow, polynomialAction_firstSimple_auxiliaryV, map_neg]
  exact neg_pow (Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU) degree

/-- Reflection negates the top axial coinvariant class. -/
theorem coinvariant_firstSimple_top (n : ℕ) [NeZero n] :
    Ideal.Quotient.mk (coinvariantIdeal n)
      (polynomialAction n (firstSimpleReflection n) (auxiliaryU ^ n)) =
      -Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n := by
  rw [coinvariant_firstSimple_auxiliaryU_pow]
  have hrelation := coinvariant_top_relation n
  have hscalar : Ideal.Quotient.mk (coinvariantIdeal n)
      (MvPolynomial.C ((-1 : ℂ) ^ n)) = (-1) ^ n := by
    simp only [map_pow, map_neg, map_one]
  rw [hscalar] at hrelation
  exact eq_neg_of_add_eq_zero_right hrelation

/-- The fundamental rotation fixes the top axial representative. -/
theorem coinvariant_rotation_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Ideal.Quotient.mk (coinvariantIdeal n)
      (polynomialAction n (rotation n) (auxiliaryU ^ n)) =
      Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n := by
  have hequal := invariant_axial_rotation_block_eigen n hthree
    (⟨0, by omega⟩ : Fin n) 1
  simpa using congrArg (Ideal.Quotient.mk (coinvariantIdeal n)) hequal

/-- Every rotation fixes the top first axial polynomial. -/
theorem polynomialAction_r_top_auxiliaryU (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (exponent : ZMod n) :
    polynomialAction n (.r exponent) (auxiliaryU ^ n) = auxiliaryU ^ n := by
  have hfixed : polynomialAction n (rotation n) (auxiliaryU ^ n) = auxiliaryU ^ n := by
    simpa using invariant_axial_rotation_block_eigen n hthree (⟨0, by omega⟩ : Fin n) 1
  have hpowers (power : ℕ) :
      polynomialAction n (rotation n ^ power) (auxiliaryU ^ n) = auxiliaryU ^ n := by
    induction power with
    | zero => simp
    | succ power hinduction =>
      rw [pow_succ, map_mul, AlgEquiv.mul_apply, hfixed, hinduction]
  have hnormal : rotation n ^ exponent.val = DihedralGroup.r exponent := by
    simp [rotation_eq_r_one, DihedralGroup.r_pow]
  rw [← hnormal]
  exact hpowers exponent.val

/-- Every reflection negates the top axial quotient class. -/
theorem coinvariant_sr_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (exponent : ZMod n) :
    Ideal.Quotient.mk (coinvariantIdeal n)
      (polynomialAction n (.sr exponent) (auxiliaryU ^ n)) =
      -Ideal.Quotient.mk (coinvariantIdeal n) auxiliaryU ^ n := by
  have hnormal : DihedralGroup.sr exponent =
      firstSimpleReflection n * DihedralGroup.r exponent := by
    simp [firstSimpleReflection, DihedralGroup.sr_mul_r]
  rw [hnormal, map_mul, AlgEquiv.mul_apply, polynomialAction_r_top_auxiliaryU n hthree]
  exact coinvariant_firstSimple_top n

end Schubert.Dihedral
