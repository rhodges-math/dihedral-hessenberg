import Schubert.Dihedral.CoinvariantBoundary
import Schubert.Dihedral.CoinvariantBasis
import Schubert.Dihedral.CoinvariantAxialRepresentation
import Schubert.Dihedral.RotationFourierSums
import Schubert.FiniteGroupCharacters.CharacterBasis

/-! # Rotation traces on the whole coinvariant algebra -/

noncomputable section
namespace Schubert.Dihedral.Coinvariant
open scoped BigOperators

/-- The whole coinvariant rotation trace has the regular-character values. -/
theorem character_r_whole (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (coordinate : ZMod n) :
    (coinvariantRepresentation n).character (.r coordinate) =
      if coordinate = 0 then 2 * (n : ℂ) else 0 := by
  classical
  let root := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)
  have hroot : root ^ n = 1 := (isPrimitiveRoot_exp_rotation_angle n).pow_eq_one
  have hpower : (root ^ coordinate.val) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hroot, one_pow]
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  have heigen : ∀ index : Fin n × Fin 2,
      coinvariantRepresentation n (.r coordinate) (basis index) =
        ((root ^ coordinate.val) ^ index.1.val) • basis index := by
    rintro ⟨index, side⟩
    by_cases hzero : index.val = 0
    · simp only [hbasis, hzero, ite_true, pow_zero, one_smul]
      fin_cases side
      · change coinvariantAction n (.r coordinate) 1 = 1
        exact map_one _
      · change coinvariantRepresentation n (.r coordinate)
          (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n)) = _
        rw [coinvariantRepresentation_mk, polynomialAction_r_top_auxiliaryU n hthree]
        rfl
    · simp only [hbasis, hzero, ite_false]
      fin_cases side
      · change coinvariantRepresentation n (.r coordinate)
          (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ (n - index.val))) =
            (root ^ coordinate.val) ^ index.val •
              Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ (n - index.val))
        rw [r_u_pow]
        have heq : (root⁻¹ ^ coordinate.val) ^ (n - index.val) =
            (root ^ coordinate.val) ^ index.val := by
          rw [inv_pow, inv_pow,
            pow_sub₀ (root ^ coordinate.val) (pow_ne_zero _ (Complex.exp_ne_zero _))
            (Nat.le_of_lt index.isLt), hpower]
          simp
        rw [show ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^
          (n - index.val) = (root ^ coordinate.val) ^ index.val from heq]
      · change coinvariantRepresentation n (.r coordinate)
          (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ index.val)) = _
        exact r_v_pow n coordinate index.val
  have htrace := Schubert.FiniteGroupCharacters.Eigenbasis.character_eq_sum
    (coinvariantRepresentation n) basis (.r coordinate)
    (fun index : Fin n × Fin 2 => (root ^ coordinate.val) ^ index.1.val) heigen
  have hsum : (coinvariantRepresentation n).character (.r coordinate) =
      2 * (∑ index : Fin n, (root ^ coordinate.val) ^ index.val) := by
    simpa only [Fintype.sum_prod_type, Fin.sum_univ_two, ← two_mul, ← Finset.mul_sum]
      using htrace
  rw [hsum]
  change 2 * (∑ index : Fin n,
    (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^ index.val) = _
  rw [rotationEigenvalue_frequency_sum_fin]
  by_cases hzero : coordinate = 0
  · subst coordinate
    simp
  · have hpositive : 0 < coordinate.val := by
      apply Nat.pos_of_ne_zero
      intro hequal
      exact hzero ((ZMod.val_eq_zero coordinate).mp hequal)
    have hnot : ¬n ∣ coordinate.val := by
      intro hdiv
      exact (not_le_of_gt coordinate.val_lt) (Nat.le_of_dvd hpositive hdiv)
    simp [hzero, hnot]

/-- Every reflection has zero trace on the whole coinvariant algebra. -/
theorem character_sr_whole (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (coordinate : ZMod n) :
    (coinvariantRepresentation n).character (.sr coordinate) = 0 := by
  classical
  obtain ⟨basis, hbasis⟩ := exists_coinvariant_axial_basis n hthree
  have hgroup : DihedralGroup.sr coordinate =
      firstSimpleReflection n * DihedralGroup.r coordinate := by
    simp [firstSimpleReflection, DihedralGroup.sr_mul_r]
  have hdiag : ∀ index : Fin n, ∑ side : Fin 2,
      basis.repr (coinvariantRepresentation n (.sr coordinate) (basis (index, side)))
        (index, side) = 0 := by
    intro index
    rw [Fin.sum_univ_two]
    by_cases hzero : index.val = 0
    · have hfirst : basis (index, 0) = 1 := by simp [hbasis, hzero]
      have hsecond : basis (index, 1) =
          Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n) := by
        simp [hbasis, hzero]
      have hone : coinvariantRepresentation n (.sr coordinate) (basis (index, 0)) =
          basis (index, 0) := by
        rw [hfirst]
        change coinvariantAction n (.sr coordinate) 1 = 1
        exact map_one _
      have htop : coinvariantRepresentation n (.sr coordinate) (basis (index, 1)) =
          -basis (index, 1) := by
        rw [hsecond, coinvariantRepresentation_mk]
        simpa only [map_pow] using coinvariant_sr_top n hthree coordinate
      simp [hone, htop]
    · have hpositive : 0 < index.val := Nat.pos_of_ne_zero hzero
      let opposite : Fin n := ⟨n - index.val, by omega⟩
      have hother : opposite.val ≠ 0 := by dsimp [opposite]; omega
      have hswap0 : basis (opposite, 1) =
          Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ (n - index.val)) := by
        simp [hbasis, hother, opposite]
      have hswap1 : basis (opposite, 0) =
          Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ index.val) := by
        simp [hbasis, hother, opposite, Nat.sub_sub_self (Nat.le_of_lt index.isLt)]
      have hvalue0 : coinvariantRepresentation n (.sr coordinate) (basis (index, 0)) =
          (((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n))⁻¹ ^ coordinate.val) ^
            (n - index.val) * (-1 : ℂ) ^ (n - index.val)) • basis (opposite, 1) := by
        rw [hbasis]
        simp only [hzero, ite_false]
        change coinvariantRepresentation n (.sr coordinate)
          (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ (n - index.val))) = _
        rw [hgroup, map_mul, Module.End.mul_apply, r_u_pow, map_smul,
          s1_u_pow, smul_smul, hswap0]
      have hvalue1 : coinvariantRepresentation n (.sr coordinate) (basis (index, 1)) =
          ((Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ coordinate.val) ^
            index.val * (-1 : ℂ) ^ index.val) • basis (opposite, 0) := by
        rw [hbasis]
        simp only [hzero, ite_false]
        change coinvariantRepresentation n (.sr coordinate)
          (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryV ^ index.val)) = _
        rw [hgroup, map_mul, Module.End.mul_apply, r_v_pow, map_smul,
          s1_v_pow, smul_smul, hswap1]
      simp [hvalue0, hvalue1, Module.Basis.repr_self]
  rw [Representation.character, LinearMap.trace_eq_matrix_trace ℂ basis]
  simp only [Matrix.trace, Fintype.sum_prod_type, Matrix.diag_apply,
    LinearMap.toMatrix_apply]
  change (∑ index : Fin n, ∑ side : Fin 2,
    basis.repr (coinvariantRepresentation n (.sr coordinate) (basis (index, side)))
      (index, side)) = 0
  simp only [hdiag, Finset.sum_const_zero]

end Schubert.Dihedral.Coinvariant
