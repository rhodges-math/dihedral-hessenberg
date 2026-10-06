import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Schubert.Dihedral.PolynomialAction

/-!
# Periodic rotations and dihedral coordinate operators

Rotations are periodic in the angle. Reduction of the rotation index modulo the polygon size
therefore agrees with addition in `ZMod`. Reflections in unit roots admit the corresponding
rotation and coordinate-reflection factorization.
-/

noncomputable section

namespace Schubert.Dihedral

/-- Adding an integral number of full turns does not change a rotation. -/
theorem complexRotation_add_nat_mul_two_pi (angle : ℝ) (turns : ℕ) :
    complexRotation (angle + turns * (2 * Real.pi)) = complexRotation angle := by
  ext vector coordinate
  fin_cases coordinate <;> simp [complexRotation]

/-- Reducing a natural rotation index modulo the polygon size preserves the operator. -/
theorem complexRotation_nat_mod (n exponent : ℕ) (hn : n ≠ 0) :
    complexRotation (2 * Real.pi * (exponent % n : ℕ) / n) =
      complexRotation (2 * Real.pi * exponent / n) := by
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdivision : ((exponent % n : ℕ) : ℝ) + n * (exponent / n : ℕ) = exponent := by
    exact_mod_cast Nat.mod_add_div exponent n
  have hangle : 2 * Real.pi * exponent / n =
      2 * Real.pi * (exponent % n : ℕ) / n + (exponent / n : ℕ) * (2 * Real.pi) := by
    rw [← hdivision]
    field_simp [hnreal]
  rw [hangle, complexRotation_add_nat_mul_two_pi]

/-- Addition of modular indices agrees with composition of coordinate rotations. -/
theorem complexRotation_zmod_add (n : ℕ) [NeZero n] (first second : ZMod n) :
    complexRotation (2 * Real.pi * (first + second).val / n) =
      (complexRotation (2 * Real.pi * first.val / n)).comp
        (complexRotation (2 * Real.pi * second.val / n)) := by
  rw [ZMod.val_add, complexRotation_nat_mod n _ (NeZero.ne n)]
  have hangle : 2 * Real.pi * (first.val + second.val : ℕ) / n =
      2 * Real.pi * first.val / n + 2 * Real.pi * second.val / n := by
    push_cast
    ring
  rw [hangle, complexRotation_add]

/-- A unit-root reflection composes coordinate reflection with rotation through minus twice
the root angle. -/
theorem complexReflection_unitRootAt (angle : ℝ) :
    complexReflection (complexify (unitRootAt angle)) =
      (complexReflection (complexify (unitRootAt 0))).comp (complexRotation (-2 * angle)) := by
  have hunit : (Real.cos angle : ℂ) ^ 2 + (Real.sin angle : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq angle
  simp only [Complex.ofReal_cos, Complex.ofReal_sin] at hunit
  apply LinearMap.ext
  intro vector
  funext coordinate
  fin_cases coordinate
  · simp only [LinearMap.comp_apply, complexReflection_apply,
      complexBilinearForm_unitRootAt, div_one]
    simp [complexRotation, unitRootAt, complexify, complexBilinearForm,
      Real.cos_two_mul, Real.sin_two_mul]
    ring
  · simp only [LinearMap.comp_apply, complexReflection_apply,
      complexBilinearForm_unitRootAt, div_one]
    simp [complexRotation, unitRootAt, complexify, complexBilinearForm,
      Real.cos_two_mul, Real.sin_two_mul]
    linear_combination -2 * vector 1 * hunit

/-- The reflection assignment agrees with coordinate reflection composed with rotation. -/
theorem vectorOperator_sr (n : ℕ) (exponent : ZMod n) :
    vectorOperator n (.sr exponent) =
      (complexReflection (complexify (unitRootAt 0))).comp
        (complexRotation (2 * Real.pi * exponent.val / n)) := by
  rw [vectorOperator, complexReflection_unitRootAt]
  congr 1
  congr 1
  ring

/-- Opposite rotations are inverse linear operators. -/
theorem complexRotation_neg_comp (angle : ℝ) :
    (complexRotation (-angle)).comp (complexRotation angle) = LinearMap.id := by
  rw [← complexRotation_add, neg_add_cancel, complexRotation_zero]

/-- Negating the modular rotation index gives the inverse angle. -/
theorem complexRotation_zmod_neg (n : ℕ) [NeZero n] (exponent : ZMod n) :
    complexRotation (2 * Real.pi * (-exponent).val / n) =
      complexRotation (-(2 * Real.pi * exponent.val / n)) := by
  calc
    complexRotation (2 * Real.pi * (-exponent).val / n) =
        LinearMap.id.comp (complexRotation (2 * Real.pi * (-exponent).val / n)) := by
      rw [LinearMap.id_comp]
    _ = ((complexRotation (-(2 * Real.pi * exponent.val / n))).comp
        (complexRotation (2 * Real.pi * exponent.val / n))).comp
          (complexRotation (2 * Real.pi * (-exponent).val / n)) := by
      rw [complexRotation_neg_comp]
    _ = (complexRotation (-(2 * Real.pi * exponent.val / n))).comp
        ((complexRotation (2 * Real.pi * exponent.val / n)).comp
          (complexRotation (2 * Real.pi * (-exponent).val / n))) :=
      LinearMap.comp_assoc _ _ _
    _ = complexRotation (-(2 * Real.pi * exponent.val / n)) := by
      rw [← complexRotation_zmod_add]
      simp [complexRotation_zero]

/-- Coordinate reflection conjugates each rotation to the opposite rotation. -/
theorem complexReflection_zero_comp_rotation (angle : ℝ) :
    (complexReflection (complexify (unitRootAt 0))).comp (complexRotation angle) =
      (complexRotation (-angle)).comp (complexReflection (complexify (unitRootAt 0))) := by
  apply LinearMap.ext
  intro vector
  funext coordinate
  fin_cases coordinate <;>
    simp [complexReflection_apply, complexRotation,
      unitRootAt, complexify, complexBilinearForm] <;> ring

/-- Modular rotations satisfy the coordinate reflection commutation relation. -/
theorem _root_.Schubert.Dihedral.Reflection.zero_comp_rotation (n : ℕ) [NeZero n] (exponent : ZMod
  n) :
    (complexReflection (complexify (unitRootAt 0))).comp
        (complexRotation (2 * Real.pi * exponent.val / n)) =
      (complexRotation (2 * Real.pi * (-exponent).val / n)).comp
        (complexReflection (complexify (unitRootAt 0))) := by
  rw [complexRotation_zmod_neg]
  exact complexReflection_zero_comp_rotation _

/-- Coordinate reflection composed with itself is the identity. -/
theorem complexReflection_zero_comp_self :
    (complexReflection (complexify (unitRootAt 0))).comp
      (complexReflection (complexify (unitRootAt 0))) = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  exact complexReflection_involutive (complexify (unitRootAt 0))
    (by rw [complexBilinearForm_unitRootAt]; exact one_ne_zero) vector

/-- The identity group element acts by the identity coordinate operator. -/
theorem vectorOperator_one (n : ℕ) : vectorOperator n 1 = LinearMap.id := by
  rw [DihedralGroup.one_def]
  simp only [vectorOperator, ZMod.val_zero, Nat.cast_zero, mul_zero, zero_div,
    complexRotation_zero]

/-- The coordinate operators preserve multiplication in the dihedral group. -/
theorem vectorOperator_mul (n : ℕ) [NeZero n] (first second : DihedralGroup n) :
    vectorOperator n (first * second) =
      (vectorOperator n first).comp (vectorOperator n second) := by
  let reflectionMap : Module.End ℂ ComplexPlane :=
    complexReflection (complexify (unitRootAt 0))
  let rotationMap : ZMod n → Module.End ℂ ComplexPlane :=
    fun exponent => complexRotation (2 * Real.pi * exponent.val / n)
  have hadd (a b : ZMod n) : rotationMap (a + b) = rotationMap a * rotationMap b :=
    complexRotation_zmod_add n a b
  have hcomm (a : ZMod n) : reflectionMap * rotationMap a =
      rotationMap (-a) * reflectionMap := _root_.Schubert.Dihedral.Reflection.zero_comp_rotation n a
  have hsquare : reflectionMap * reflectionMap = 1 := complexReflection_zero_comp_self
  cases first with
  | r a =>
    cases second with
    | r b => exact hadd a b
    | sr b =>
      simp only [DihedralGroup.r_mul_sr, vectorOperator_sr]
      change reflectionMap * rotationMap (b - a) =
        rotationMap a * (reflectionMap * rotationMap b)
      rw [show b - a = -a + b by abel, hadd, ← mul_assoc, hcomm, neg_neg, mul_assoc]
  | sr a =>
    cases second with
    | r b =>
      simp only [DihedralGroup.sr_mul_r, vectorOperator_sr]
      change reflectionMap * rotationMap (a + b) =
        (reflectionMap * rotationMap a) * rotationMap b
      rw [hadd, mul_assoc]
    | sr b =>
      simp only [DihedralGroup.sr_mul_sr, vectorOperator_sr]
      change rotationMap (b - a) =
        (reflectionMap * rotationMap a) * (reflectionMap * rotationMap b)
      rw [hcomm a, mul_assoc, ← mul_assoc reflectionMap reflectionMap, hsquare,
        one_mul, ← hadd]
      congr 1
      abel

/-- The coordinate realization as a complex representation of the dihedral group. -/
def vectorRepresentation (n : ℕ) [NeZero n] :
    Representation ℂ (DihedralGroup n) ComplexPlane where
  toFun := vectorOperator n
  map_one' := vectorOperator_one n
  map_mul' := vectorOperator_mul n

/-- The dihedral polynomial operators bundled as an action by algebra endomorphisms. -/
def polynomialEndomorphismAction (n : ℕ) [NeZero n] :
    DihedralGroup n →* (CoordinatePolynomial →ₐ[ℂ] CoordinatePolynomial) where
  toFun := polynomialOperator n
  map_one' := by
    change polynomialSubstitution (vectorOperator n 1) = AlgHom.id ℂ CoordinatePolynomial
    rw [vectorOperator_one, polynomialSubstitution_id]
  map_mul' := by
    intro first second
    change polynomialSubstitution (vectorOperator n (first * second)) =
      (polynomialSubstitution (vectorOperator n first)).comp
        (polynomialSubstitution (vectorOperator n second))
    rw [vectorOperator_mul, polynomialSubstitution_comp]

/-- The dihedral polynomial action by algebra automorphisms. -/
def polynomialAction (n : ℕ) [NeZero n] :
    DihedralGroup n →* (CoordinatePolynomial ≃ₐ[ℂ] CoordinatePolynomial) :=
  (AlgEquiv.algHomUnitsEquiv ℂ CoordinatePolynomial).toMonoidHom.comp
    (polynomialEndomorphismAction n).toHomUnits

theorem polynomialAction_apply (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    polynomialAction n element polynomial = polynomialOperator n element polynomial :=
  rfl

/-- The polynomial action carries a vector's linear polynomial to that of its vector image. -/
theorem polynomialAction_linearPolynomial (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (vector : ComplexPlane) :
    polynomialAction n element (linearPolynomial vector) =
      linearPolynomial (vectorOperator n element vector) :=
  polynomialSubstitution_linearPolynomial (vectorOperator n element) vector

end Schubert.Dihedral
