import DihedralHessenberg.Dihedral.RootPreservation

/-! # Signs of roots in the existing angular realization -/

namespace Schubert.Dihedral

/-- Complexification is injective on the real coordinate plane. -/
theorem complexify_injective : Function.Injective complexify := by
  intro first second heq
  funext coordinate
  have hcoordinate := congrFun heq coordinate
  exact Complex.ofReal_inj.mp hcoordinate

/-- In a full turn, a lattice root is positive exactly in the first half-turn. -/
theorem unitRootAt_nat_mem_positiveRoots_iff (n position : ℕ) [NeZero n]
    (hposition : position < 2 * n) :
    unitRootAt ((position : ℝ) * Real.pi / n) ∈ positiveRoots n ↔ position < n := by
  by_cases hhalf : position < n
  · exact ⟨fun _ => hhalf, fun _ => unitRootAt_nat_mem_positiveRoots n position hhalf⟩
  · constructor
    · intro hpositive
      have hupper : position - n < n := by omega
      have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
      have hangle : (position : ℝ) * Real.pi / n =
          (position - n : ℕ) * Real.pi / n + Real.pi := by
        rw [Nat.cast_sub (Nat.le_of_not_gt hhalf)]
        field_simp [hnreal]
        ring
      have hnegative : unitRootAt ((position : ℝ) * Real.pi / n) =
          -unitRootAt ((position - n : ℕ) * Real.pi / n) := by
        rw [hangle, unitRootAt_add_pi]
      obtain ⟨first, hfirst⟩ := hpositive
      obtain ⟨second, hsecond⟩ := unitRootAt_nat_mem_positiveRoots n (position - n) hupper
      exact (positiveRoot_ne_neg n first second
        (hfirst.trans (hnegative.trans (congrArg Neg.neg hsecond).symm))).elim
    · exact fun h => (hhalf h).elim

/-- Reducing an integer angular position modulo a full turn preserves the root vector. -/
theorem unitRootAt_int_eq_emod (n : ℕ) [NeZero n] (position : ℤ) :
    unitRootAt ((position : ℝ) * Real.pi / n) =
      unitRootAt (((position % (2 * n : ℤ) : ℤ) : ℝ) * Real.pi / n) := by
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hdivision : (position : ℝ) = ((position % (2 * n : ℤ) : ℤ) : ℝ) +
      2 * n * ((position / (2 * n : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv position (2 * n : ℤ)).symm
  have hangle : (position : ℝ) * Real.pi / n =
      ((position % (2 * n : ℤ) : ℤ) : ℝ) * Real.pi / n +
        ((position / (2 * n : ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hdivision]
    field_simp [hnreal]
  rw [hangle]
  apply realPlane_ext <;> simp [unitRootAt]

/-- An integer lattice root is positive exactly when its full-turn residue is below n. -/
theorem unitRootAt_int_mem_positiveRoots_iff (n : ℕ) [NeZero n] (position : ℤ) :
    unitRootAt ((position : ℝ) * Real.pi / n) ∈ positiveRoots n ↔
      position % (2 * n : ℤ) < n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmodulus : (0 : ℤ) < 2 * n := by omega
  have hnonneg := Int.emod_nonneg position hmodulus.ne'
  have hupper := Int.emod_lt_of_pos position hmodulus
  let remainder := (position % (2 * n : ℤ)).toNat
  have hremainder : (remainder : ℤ) = position % (2 * n : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hsmall : remainder < 2 * n := by omega
  rw [unitRootAt_int_eq_emod, ← hremainder]
  norm_cast
  rw [unitRootAt_nat_mem_positiveRoots_iff n remainder hsmall]

/-- Rotation adds twice its modular exponent to the integer angular root position. -/
theorem vectorOperator_r_complexPositiveRoot (n : ℕ) (exponent : ZMod n)
    (index : PositiveRootIndex n) :
    vectorOperator n (.r exponent) (complexPositiveRoot n index) =
      complexify (unitRootAt
        (((angularIndex index + 2 * exponent.val : ℕ) : ℝ) * Real.pi / n)) := by
  rw [complexPositiveRoot, positiveRoot, rootAngle_eq_angularIndex,
    vectorOperator, complexRotation_complexify_unitRootAt]
  congr 2
  push_cast
  ring

/-- Reflection acts affinely on the integer angular root position. -/
theorem vectorOperator_sr_complexPositiveRoot (n : ℕ) [NeZero n]
    (exponent : ZMod n) (index : PositiveRootIndex n) :
    vectorOperator n (.sr exponent) (complexPositiveRoot n index) =
      complexify (unitRootAt
        (((n - angularIndex index - 2 * exponent.val : ℤ) : ℝ) * Real.pi / n)) := by
  rw [complexPositiveRoot, positiveRoot, rootAngle_eq_angularIndex,
    vectorOperator_sr_complexify_unitRootAt]
  congr 2
  push_cast
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp [hnreal]
  ring

/-- A rotated positive root stays positive exactly in the first angular half-turn. -/
theorem vectorOperator_r_mem_positiveRoots_iff (n : ℕ) [NeZero n]
    (exponent : ZMod n) (index : PositiveRootIndex n) :
    (fun coordinate =>
      (vectorOperator n (.r exponent) (complexPositiveRoot n index) coordinate).re) ∈
        positiveRoots n ↔
      (angularIndex index + 2 * exponent.val : ℤ) % (2 * n : ℤ) < n := by
  rw [vectorOperator_r_complexPositiveRoot]
  simp only [complexify, Complex.ofReal_re]
  have hsign := unitRootAt_int_mem_positiveRoots_iff n
    (angularIndex index + 2 * exponent.val : ℤ)
  push_cast at hsign ⊢
  exact hsign

/-- A reflected positive root stays positive exactly in the first angular half-turn. -/
theorem vectorOperator_sr_mem_positiveRoots_iff (n : ℕ) [NeZero n]
    (exponent : ZMod n) (index : PositiveRootIndex n) :
    (fun coordinate =>
      (vectorOperator n (.sr exponent) (complexPositiveRoot n index) coordinate).re) ∈
        positiveRoots n ↔
      (n - angularIndex index - 2 * exponent.val : ℤ) % (2 * n : ℤ) < n := by
  rw [vectorOperator_sr_complexPositiveRoot]
  simp only [complexify, Complex.ofReal_re]
  exact unitRootAt_int_mem_positiveRoots_iff n _

end Schubert.Dihedral
