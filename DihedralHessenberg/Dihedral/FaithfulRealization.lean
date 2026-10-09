import DihedralHessenberg.Dihedral.InvariantsBasic
import DihedralHessenberg.Dihedral.RootObjects

/-! # Faithfulness of the coordinate reflection representation -/

namespace Schubert.Dihedral

/-- Only the identity group element acts as the identity coordinate operator. -/
theorem vectorOperator_eq_id (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (hoperator : vectorOperator n element = LinearMap.id) : element = 1 := by
  cases element with
  | r coordinate =>
    have haction : polynomialAction n (.r coordinate) auxiliaryV = auxiliaryV := by
      rw [polynomialAction_apply]
      change polynomialSubstitution (vectorOperator n (.r coordinate)) auxiliaryV = auxiliaryV
      rw [hoperator, polynomialSubstitution_id, AlgHom.id_apply]
    rw [polynomialAction_r_auxiliaryV] at haction
    have hscalar := congrArg
      (MvPolynomial.eval (fun position : Fin 2 => if position = 0 then (1 : ℂ) else 0)) haction
    simp only [map_mul, MvPolynomial.eval_C] at hscalar
    have hvalue : MvPolynomial.eval
        (fun position : Fin 2 => if position = 0 then (1 : ℂ) else 0) auxiliaryV = 1 := by
      norm_num [auxiliaryV]
    rw [hvalue, mul_one] at hscalar
    have hangle : (((2 * Real.pi * coordinate.val / n : ℝ) : ℂ) * Complex.I) =
        (coordinate.val : ℂ) * (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hangle, Complex.exp_nat_mul] at hscalar
    have hdiv := ((isPrimitiveRoot_rotationEigenvalue n).pow_eq_one_iff_dvd coordinate.val).mp
      hscalar
    have hzero : coordinate.val = 0 := Nat.eq_zero_of_dvd_of_lt hdiv (ZMod.val_lt coordinate)
    rw [(ZMod.val_eq_zero coordinate).mp hzero, DihedralGroup.r_zero]
  | sr coordinate =>
    let normal := complexify (unitRootAt (-Real.pi * coordinate.val / n))
    have hunit : complexBilinearForm normal normal = 1 := complexBilinearForm_unitRootAt _
    have hflip : vectorOperator n (.sr coordinate) normal = -normal :=
      complexReflection_normal normal (by rw [hunit]; norm_num)
    rw [hoperator, LinearMap.id_apply] at hflip
    have hzero (position : Fin 2) : normal position = 0 := by
      have heq := congrFun hflip position
      change normal position = -normal position at heq
      have htwice : (2 : ℂ) * normal position = 0 := by
        linear_combination heq
      exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)
    simp only [complexBilinearForm, hzero, mul_zero, zero_add] at hunit
    exact False.elim (zero_ne_one hunit)

/-- The group embeds faithfully into its complex coordinate operators. -/
theorem vectorOperator_injective (n : ℕ) [NeZero n] :
    Function.Injective (vectorOperator n) := by
  change Function.Injective (vectorRepresentation n)
  apply (injective_iff_map_eq_one (vectorRepresentation n)).mpr
  intro element heq
  exact vectorOperator_eq_id n element heq

private theorem reflection_complexify (normal vector : RealPlane) :
    complexReflection (complexify normal) (complexify vector) =
      complexify (vector - (2 * realBilinearForm vector normal /
        realBilinearForm normal normal) • normal) := by
  rw [complexReflection_apply, complexBilinearForm_complexify,
    complexBilinearForm_complexify]
  funext position
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, complexify,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The coordinate operator preserves the entire real plane, with its specified real action. -/
theorem realAction_complexify_plane (n : ℕ) (element : DihedralGroup n)
    (vector : RealPlane) :
    complexify (realAction n element vector) = vectorOperator n element (complexify vector) := by
  have himage : ∃ image : RealPlane,
      vectorOperator n element (complexify vector) = complexify image := by
    cases element with
    | r coordinate =>
      let angle := 2 * Real.pi * coordinate.val / n
      refine ⟨![Real.cos angle * vector 0 - Real.sin angle * vector 1,
        Real.sin angle * vector 0 + Real.cos angle * vector 1], ?_⟩
      apply complexPlane_ext <;> simp [vectorOperator, complexRotation, complexify, angle]
    | sr coordinate =>
      let normal := unitRootAt (-Real.pi * coordinate.val / n)
      refine ⟨vector - (2 * realBilinearForm vector normal /
        realBilinearForm normal normal) • normal, ?_⟩
      exact reflection_complexify normal vector
  obtain ⟨image, heq⟩ := himage
  change complexify (fun position =>
    (vectorOperator n element (complexify vector) position).re) = _
  simp only [heq, complexify, Complex.ofReal_re]

/-- The group acts faithfully on the entire real coordinate plane. -/
theorem realAction_injective (n : ℕ) [NeZero n] : Function.Injective (realAction n) := by
  intro first second heq
  apply vectorOperator_injective n
  have hbasis (position : Fin 2) :
      vectorOperator n first (coordinateBasisVector position) =
        vectorOperator n second (coordinateBasisVector position) := by
    let vector : RealPlane := Pi.single position 1
    have hcomplex : complexify vector = coordinateBasisVector position := by
      funext coordinate
      simp [complexify, vector, coordinateBasisVector, Pi.single_apply]
      split_ifs <;> norm_num
    have haction := congrArg complexify (congrFun heq vector)
    rw [realAction_complexify_plane, realAction_complexify_plane, hcomplex] at haction
    exact haction
  apply LinearMap.ext
  intro vector
  rw [vector_eq_coordinate_expansion vector]
  simp only [map_add, map_smul, hbasis]

/-- Multiplication composes the real action on every vector in the plane. -/
theorem realAction_mul_plane (n : ℕ) [NeZero n] (first second : DihedralGroup n)
    (vector : RealPlane) :
    realAction n (first * second) vector = realAction n first (realAction n second vector) := by
  have heq : complexify (realAction n (first * second) vector) =
      complexify (realAction n first (realAction n second vector)) := by
    rw [realAction_complexify_plane, realAction_complexify_plane,
      realAction_complexify_plane, vectorOperator_mul, LinearMap.comp_apply]
  funext coordinate
  exact Complex.ofReal_injective (congrFun heq coordinate)

/-- Each positive root acts as its Euclidean normal reflection on the whole plane. -/
theorem PositiveRoot.realAction_reflection {n : ℕ} (alpha : PositiveRoot n)
    (vector : RealPlane) :
    realAction n alpha.reflection vector =
      vector - (2 * realBilinearForm vector alpha.val) • alpha.val := by
  have hunit : realBilinearForm alpha.val alpha.val = 1 := by
    rw [← alpha.index_val]
    exact positiveRoot_unit n alpha.index
  have heq : complexify (realAction n alpha.reflection vector) =
      complexify (vector - (2 * realBilinearForm vector alpha.val) • alpha.val) := by
    rw [realAction_complexify_plane, alpha.reflection_operator,
      reflection_complexify, hunit, div_one]
  funext coordinate
  exact Complex.ofReal_injective (congrFun heq coordinate)

end Schubert.Dihedral
