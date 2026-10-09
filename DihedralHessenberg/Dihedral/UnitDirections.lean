import DihedralHessenberg.Dihedral.FaithfulRealization
import DihedralHessenberg.Dihedral.RootFixedHyperplane

/-! # Angular action on real unit directions -/

namespace Schubert.Dihedral

/-- A dihedral rotation adds its modular angle to a real unit direction. -/
theorem realAction_r_unit (n : ℕ) (coordinate : ZMod n) (angle : ℝ) :
    realAction n (.r coordinate) (unitRootAt angle) =
      unitRootAt (2 * Real.pi * coordinate.val / n + angle) := by
  apply realPlane_ext <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, realAction, vectorOperator,
      complexRotation, unitRootAt, complexify,
      Real.cos_add, Real.sin_add]

/-- A dihedral reflection reverses the angle after applying its modular rotation. -/
theorem realAction_sr_unit (n : ℕ) (coordinate : ZMod n) (angle : ℝ) :
    realAction n (.sr coordinate) (unitRootAt angle) =
      unitRootAt (Real.pi - (2 * Real.pi * coordinate.val / n + angle)) := by
  unfold realAction
  rw [vectorOperator_sr]
  apply realPlane_ext <;>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, LinearMap.comp_apply, complexReflection,
      complexRotation, complexBilinearForm, complexPairing,
      unitRootAt, complexify, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_add, Real.sin_add]
  ring

/-- Integral full turns do not change a real unit direction. -/
theorem unitRootAt_add_turns (angle : ℝ) (turns : ℕ) :
    unitRootAt (angle + turns * (2 * Real.pi)) = unitRootAt angle := by
  apply realPlane_ext <;> simp [unitRootAt]

/-- A shifted regularly spaced direction depends only on its modular index. -/
theorem unitRootAt_nat_mod (n coordinate : ℕ) (hn : n ≠ 0) (offset : ℝ) :
    unitRootAt (2 * Real.pi * (coordinate % n : ℕ) / n + offset) =
      unitRootAt (2 * Real.pi * coordinate / n + offset) := by
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdivision : ((coordinate % n : ℕ) : ℝ) + n * (coordinate / n : ℕ) = coordinate := by
    exact_mod_cast Nat.mod_add_div coordinate n
  have hangle : 2 * Real.pi * coordinate / n + offset =
      (2 * Real.pi * (coordinate % n : ℕ) / n + offset) +
        (coordinate / n : ℕ) * (2 * Real.pi) := by
    rw [← hdivision]
    field_simp [hnreal]
    ring
  rw [hangle, unitRootAt_add_turns]


/-- A rotation fixes a real unit vector only when its modular index is zero. -/
theorem rotation_fixed_unit (n : ℕ) [NeZero n] (coordinate : ZMod n) (vector : RealPlane)
    (hunit : realBilinearForm vector vector = 1)
    (hfixed : realAction n (.r coordinate) vector = vector) : coordinate = 0 := by
  let angle := 2 * Real.pi * coordinate.val / n
  have hzero := congrFun hfixed 0
  have hone := congrFun hfixed 1
  simp only [realAction, vectorOperator, complexRotation, LinearMap.pi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, complexify,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.sub_re, Complex.add_re] at hzero hone
  change Real.cos angle * vector 0 - Real.sin angle * vector 1 = vector 0 at hzero
  change Real.sin angle * vector 0 + Real.cos angle * vector 1 = vector 1 at hone
  have hnorm : vector 0 * vector 0 + vector 1 * vector 1 = 1 := hunit
  have hcos_zero : (Real.cos angle - 1) * (vector 0 * vector 0 + vector 1 * vector 1) = 0 := by
    linear_combination vector 0 * hzero + vector 1 * hone
  have hsin_zero : Real.sin angle * (vector 0 * vector 0 + vector 1 * vector 1) = 0 := by
    linear_combination vector 0 * hone - vector 1 * hzero
  rw [hnorm, mul_one, sub_eq_zero] at hcos_zero
  rw [hnorm, mul_one] at hsin_zero
  have hoperator : vectorOperator n (.r coordinate) = LinearMap.id := by
    dsimp only [angle] at hcos_zero hsin_zero
    apply LinearMap.ext
    intro point
    funext position
    fin_cases position <;> simp [-ZMod.natCast_val, -Complex.ofReal_cos, -Complex.ofReal_sin,
      vectorOperator, complexRotation, hcos_zero, hsin_zero]
  have helement := vectorOperator_eq_id n (.r coordinate) hoperator
  rw [← DihedralGroup.r_zero, DihedralGroup.r.injEq] at helement
  exact helement


/-- The real coordinate action preserves real scalar multiples on the entire plane. -/
theorem realAction_smul_plane (n : ℕ) (element : DihedralGroup n) (scalar : ℝ)
    (vector : RealPlane) :
    realAction n element (scalar • vector) = scalar • realAction n element vector := by
  have hcomplex : complexify (scalar • vector) = (scalar : ℂ) • complexify vector := by
    funext position
    simp only [complexify, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  funext position
  unfold realAction
  rw [hcomplex, map_smul]
  simp [Pi.smul_apply, smul_eq_mul, Complex.mul_re]

/-- The positive roots are the equally spaced unit directions in a half-turn. -/
theorem positiveRoots_unit_angles (n : ℕ) :
    positiveRoots n = Set.range (fun index : Fin n =>
      unitRootAt (index.val * Real.pi / n)) := by
  ext vector
  constructor
  · rintro ⟨index, rfl⟩
    refine ⟨⟨angularIndex index, angularIndex_lt index⟩, ?_⟩
    exact (congrArg unitRootAt (rootAngle_eq_angularIndex n index)).symm
  · rintro ⟨index, rfl⟩
    exact unitRootAt_nat_mem_positiveRoots n index.val index.isLt


/-- Every real point on the root's orthogonal axis is fixed by its reflection. -/
theorem PositiveRoot.reflection_axis {n : ℕ} (alpha : PositiveRoot n) (scalar : ℝ) :
    realAction n alpha.reflection (scalar • ![-alpha.val 1, alpha.val 0]) =
      scalar • ![-alpha.val 1, alpha.val 0] := by
  apply (alpha.reflection_fixed _).mpr
  simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring


/-- The fixed vectors of a root reflection form exactly its orthogonal real axis. -/
theorem PositiveRoot.fixed_iff_axis {n : ℕ} (alpha : PositiveRoot n) (vector : RealPlane) :
    realAction n alpha.reflection vector = vector ↔
      ∃ scalar : ℝ, vector = scalar • ![-alpha.val 1, alpha.val 0] := by
  rw [alpha.reflection_fixed]
  have hunit := roots_unit alpha.val (Or.inl alpha.property)
  change alpha.val 0 * alpha.val 0 + alpha.val 1 * alpha.val 1 = 1 at hunit
  constructor
  · intro horthogonal
    change vector 0 * alpha.val 0 + vector 1 * alpha.val 1 = 0 at horthogonal
    refine ⟨alpha.val 0 * vector 1 - alpha.val 1 * vector 0, ?_⟩
    apply realPlane_ext
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
      linear_combination -vector 0 * hunit + alpha.val 0 * horthogonal
    · simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
      linear_combination -vector 1 * hunit + alpha.val 1 * horthogonal
  · rintro ⟨scalar, rfl⟩
    simp only [realBilinearForm, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    ring


/-- Every dihedral coordinate action preserves the Euclidean bilinear pairing of real vectors. -/
theorem realAction_pairing (n : ℕ) (element : DihedralGroup n) (first second : RealPlane) :
    realBilinearForm (realAction n element first) (realAction n element second) =
      realBilinearForm first second := by
  cases element with
  | r coordinate =>
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, realBilinearForm, realAction,
      vectorOperator, complexRotation, complexify]
    linear_combination (first 0 * second 0 + first 1 * second 1) *
      Real.sin_sq_add_cos_sq (2 * Real.pi * coordinate.val / n)
  | sr coordinate =>
    unfold realAction
    rw [vectorOperator_sr]
    simp [-Complex.ofReal_cos, -Complex.ofReal_sin, realBilinearForm, LinearMap.comp_apply,
      complexReflection, complexRotation, complexPairing, complexBilinearForm,
      complexify, unitRootAt]
    linear_combination (first 0 * second 0 + first 1 * second 1) *
      Real.sin_sq_add_cos_sq (2 * Real.pi * coordinate.val / n)

end Schubert.Dihedral
