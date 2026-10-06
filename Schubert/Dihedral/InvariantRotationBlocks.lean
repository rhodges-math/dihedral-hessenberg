import Schubert.Dihedral.FundamentalEigenvalues
import Schubert.Dihedral.InvariantAxialIndependence
import Schubert.Dihedral.InvariantRotationSeparation

/-! # Rotation blocks in the auxiliary spanning family

The 2n axial vectors fall into n pairs with distinct rotation eigenvalues.
Independence within a pair and separation between eigenspaces give full independence.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Independent pairs in distinct rotation eigenspaces are independent over invariants. -/
theorem _root_.Schubert.Dihedral.Invariants.rotation_pairs_independent (n : ℕ) [NeZero n]
    (family : Fin n → Fin 2 → CoordinatePolynomial)
    (hpairs : ∀ index, LinearIndependent (invariantSubalgebra n) (family index))
    (heigen : ∀ index coordinate, polynomialAction n (rotation n) (family index coordinate) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val • family index coordinate) :
    LinearIndependent (invariantSubalgebra n)
      (fun index : Fin n × Fin 2 => family index.1 index.2) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients hsum
  let components (index : Fin n) := ∑ coordinate : Fin 2,
    coefficients (index, coordinate) • family index coordinate
  have hcomponents : ∀ index, polynomialAction n (rotation n) (components index) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val • components index := by
    intro index
    simp only [components, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    have hfixed : polynomialAction n (rotation n)
        (coefficients (index, coordinate) : CoordinatePolynomial) =
        coefficients (index, coordinate) :=
      (mem_invariantSubalgebra n _).mp (coefficients (index, coordinate)).property _
    change polynomialAction n (rotation n)
      ((coefficients (index, coordinate) : CoordinatePolynomial) * family index coordinate) = _
    rw [map_mul, hfixed, heigen]
    simp only [Algebra.smul_def, Subalgebra.algebraMap_apply]
    ring
  have hsumComponents : ∑ index, components index = 0 := by
    simpa only [components, Fintype.sum_prod_type] using hsum
  have hzero := rotation_eigencomponents_eq_zero n components hcomponents hsumComponents
  intro index
  exact Fintype.linearIndependent_iff.mp (hpairs index.1)
    (fun coordinate => coefficients (index.1, coordinate)) (hzero index.1) index.2

/-- Complementary inverse powers of the primitive eigenvalue equal its positive powers. -/
theorem rotationEigenvalue_inverse_complement (n : ℕ) [NeZero n] (index : Fin n) :
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ (n - index.val) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val := by
  let eigenvalue := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hnonzero : eigenvalue ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ (pow_ne_zero (n - index.val) hnonzero)
  change eigenvalue ^ (n - index.val) * eigenvalue⁻¹ ^ (n - index.val) =
    eigenvalue ^ (n - index.val) * eigenvalue ^ index.val
  rw [← mul_pow, mul_inv_cancel₀ hnonzero, one_pow, ← pow_add,
    Nat.sub_add_cancel index.isLt.le]
  exact (isPrimitiveRoot_exp_rotation_angle n).pow_eq_one.symm

/-- Each axial rotation block has the positive rotation eigenvalue indexed by its block. -/
theorem invariant_axial_rotation_block_eigen (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (index : Fin n) (coordinate : Fin 2) :
    polynomialAction n (rotation n)
      ((if index.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
        else ![auxiliaryU ^ (n - index.val), auxiliaryV ^ index.val]) coordinate) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val •
        ((if index.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
          else ![auxiliaryU ^ (n - index.val), auxiliaryV ^ index.val]) coordinate) := by
  by_cases hzero : index.val = 0
  · simp only [hzero, ite_true, pow_zero, one_smul]
    fin_cases coordinate
    · exact map_one _
    · change polynomialAction n (rotation n) (auxiliaryU ^ n) = auxiliaryU ^ n
      rw [map_pow, polynomialAction_rotation_auxiliaryU n hthree, mul_pow, ← map_pow]
      have hinverse : (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ n = 1 := by
        rw [inv_pow, (isPrimitiveRoot_exp_rotation_angle n).pow_eq_one, inv_one]
      simp [hinverse]
  · simp only [hzero, ite_false]
    fin_cases coordinate
    · change polynomialAction n (rotation n) (auxiliaryU ^ (n - index.val)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val •
          auxiliaryU ^ (n - index.val)
      rw [map_pow, polynomialAction_rotation_auxiliaryU n hthree, mul_pow, ← map_pow,
        rotationEigenvalue_inverse_complement]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]
    · change polynomialAction n (rotation n) (auxiliaryV ^ index.val) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val •
          auxiliaryV ^ index.val
      rw [map_pow, polynomialAction_rotation_auxiliaryV n hthree, mul_pow, ← map_pow]
      simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq]

set_option maxHeartbeats 2000000 in
/-- The axial rotation blocks are linearly independent over the invariant algebra. -/
theorem _root_.Schubert.Dihedral.Invariants.axial_blocks_independent (n : ℕ) [NeZero n]
    (hthree : 3 ≤ n) :
    LinearIndependent (invariantSubalgebra n) (fun index : Fin n × Fin 2 =>
      (if index.1.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
        else ![auxiliaryU ^ (n - index.1.val), auxiliaryV ^ index.1.val]) index.2) := by
  refine _root_.Schubert.Dihedral.Invariants.rotation_pairs_independent n
    (fun index : Fin n => if index.val = 0 then ![(1 : CoordinatePolynomial), auxiliaryU ^ n]
      else ![auxiliaryU ^ (n - index.val), auxiliaryV ^ index.val]) ?_ ?_
  · intro index
    by_cases hzero : index.val = 0
    · simp only [hzero, ite_true]
      exact LinearIndependent.pair_symm_iff.mp
        (by simpa only [pow_zero] using
          invariant_axial_pair_linearIndependent n n 0 (by omega))
    · simp only [hzero, ite_false]
      exact invariant_axial_pair_linearIndependent n (n - index.val) index.val (by omega)
  · exact invariant_axial_rotation_block_eigen n hthree

end Schubert.Dihedral
