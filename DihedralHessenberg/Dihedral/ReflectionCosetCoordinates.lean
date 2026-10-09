import DihedralHessenberg.Dihedral.ReflectionCosetRepresentation

/-! # Rotation coordinates on the reflection cosets -/

namespace Schubert.Dihedral

variable {n : ℕ}

/-- The reflection coset represented by a rotation. -/
def rotationCoset (index : PositiveRootIndex n) (coordinate : ZMod n) :
    RootReflectionCosets index := QuotientGroup.mk (DihedralGroup.r coordinate)

/-- Rotations represent distinct reflection cosets. -/
theorem rotationCoset_injective [NeZero n] (index : PositiveRootIndex n) :
    Function.Injective (rotationCoset index) := by
  intro first second heq
  have hmem := QuotientGroup.eq.mp heq
  change (DihedralGroup.r first)⁻¹ * DihedralGroup.r second ∈
    Subgroup.closure {rootReflection index} at hmem
  rw [rootReflection_eq_sr, DihedralGroup.inv_r, DihedralGroup.r_mul_r,
    mem_closure_sr_iff] at hmem
  rcases hmem with hone | hreflection
  · have hzero : -first + second = 0 := DihedralGroup.r.inj hone
    linear_combination -hzero
  · cases hreflection

/-- A reflection coset has its explicit rotation representative. -/
theorem reflection_coset_eq_rotationCoset (index : PositiveRootIndex n) (coordinate : ZMod n) :
    (QuotientGroup.mk (DihedralGroup.sr coordinate) : RootReflectionCosets index) =
      rotationCoset index (reflectionCoordinate index - coordinate) := by
  have hfactor : DihedralGroup.sr coordinate =
      DihedralGroup.r (reflectionCoordinate index - coordinate) * rootReflection index := by
    rw [rootReflection_eq_sr, DihedralGroup.r_mul_sr]
    congr 1
    ring
  rw [hfactor]
  apply QuotientGroup.mk_mul_of_mem
  exact Subgroup.subset_closure (Set.mem_singleton _)

/-- Every reflection coset has a rotation representative. -/
theorem rotationCoset_surjective (index : PositiveRootIndex n) :
    Function.Surjective (rotationCoset index) := by
  intro coset
  obtain ⟨element, rfl⟩ := QuotientGroup.mk_surjective coset
  cases element with
  | r coordinate => exact ⟨coordinate, rfl⟩
  | sr coordinate =>
    exact ⟨reflectionCoordinate index - coordinate,
      (reflection_coset_eq_rotationCoset index coordinate).symm⟩

/-- Rotation representatives identify the reflection cosets with cyclic coordinates. -/
noncomputable def rotationCosetEquiv [NeZero n] (index : PositiveRootIndex n) :
    ZMod n ≃ RootReflectionCosets index :=
  Equiv.ofBijective (rotationCoset index)
    ⟨rotationCoset_injective index, rotationCoset_surjective index⟩

/-- A rotation acts on reflection cosets by addition in the rotation coordinates. -/
theorem r_smul_rotationCoset (index : PositiveRootIndex n) (first second : ZMod n) :
    DihedralGroup.r first • rotationCoset index second = rotationCoset index (first + second) := by
  change QuotientGroup.mk (DihedralGroup.r first * DihedralGroup.r second) = _
  rw [DihedralGroup.r_mul_r]
  rfl

/-- A reflection acts by the affine involution determined by the generating reflection. -/
theorem sr_smul_rotationCoset (index : PositiveRootIndex n) (first second : ZMod n) :
    DihedralGroup.sr first • rotationCoset index second =
      rotationCoset index (reflectionCoordinate index - first - second) := by
  change QuotientGroup.mk (DihedralGroup.sr first * DihedralGroup.r second) = _
  rw [DihedralGroup.sr_mul_r, reflection_coset_eq_rotationCoset]
  congr 1
  ring

/-- A rotation fixes a reflection coset exactly when the rotation is the identity. -/
theorem r_smul_rotationCoset_eq_iff [NeZero n] (index : PositiveRootIndex n)
    (first second : ZMod n) :
    DihedralGroup.r first • rotationCoset index second = rotationCoset index second ↔
      first = 0 := by
  rw [r_smul_rotationCoset, (rotationCoset_injective index).eq_iff]
  exact add_eq_right

/-- Reflection-fixed cosets correspond exactly to a cyclic-coordinate doubling equation. -/
theorem sr_smul_rotationCoset_eq_iff [NeZero n] (index : PositiveRootIndex n)
    (first second : ZMod n) :
    DihedralGroup.sr first • rotationCoset index second = rotationCoset index second ↔
      2 * second = reflectionCoordinate index - first := by
  rw [sr_smul_rotationCoset, (rotationCoset_injective index).eq_iff]
  constructor <;> intro heq <;> linear_combination -heq

end Schubert.Dihedral
