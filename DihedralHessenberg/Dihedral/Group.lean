import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# Simple reflections and indexed reflections of a dihedral group

The two distinguished simple reflections of `DihedralGroup n` are `sr 0` and `sr 1`.
Their product is the rotation `r 1`. Positive-root indices are zero-based: index `i`
corresponds to the root numbered `i.val + 1`. The associated reflections are defined
by alternating words in the two simple reflections.
-/

namespace Schubert.Dihedral

/-- The first distinguished simple reflection of the dihedral group. -/
def firstSimpleReflection (n : ℕ) : DihedralGroup n := DihedralGroup.sr 0

/-- The second distinguished simple reflection of the dihedral group. -/
def secondSimpleReflection (n : ℕ) : DihedralGroup n := DihedralGroup.sr 1

/-- The simple reflections, indexed by `Fin 2` in their distinguished order. -/
def simpleReflection (n : ℕ) (i : Fin 2) : DihedralGroup n :=
  if i = 0 then firstSimpleReflection n else secondSimpleReflection n

/-- The rotation that is the product of the first and second simple reflections. -/
def rotation (n : ℕ) : DihedralGroup n :=
  firstSimpleReflection n * secondSimpleReflection n

/-- The index of a positive root; index `i` denotes the root numbered `i.val + 1`. -/
abbrev PositiveRootIndex (n : ℕ) := Fin n

/-- The first simple-root index in a dihedral root system with at least three roots. -/
def firstSimpleRootIndex (n : ℕ) (hthree : 3 ≤ n) : PositiveRootIndex n :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 3) hthree⟩

/-- The second simple-root index in a dihedral root system with at least three roots. -/
def secondSimpleRootIndex (n : ℕ) (hthree : 3 ≤ n) : PositiveRootIndex n :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 3) hthree⟩

/-- The reflection associated to a positive-root index.
Even indices give `(s₁s₂)^k s₁`; odd indices give `(s₂s₁)^k s₂`. -/
def rootReflection {n : ℕ} (i : PositiveRootIndex n) : DihedralGroup n :=
  if i.val % 2 = 0 then
    (firstSimpleReflection n * secondSimpleReflection n) ^ (i.val / 2) *
      firstSimpleReflection n
  else
    (secondSimpleReflection n * firstSimpleReflection n) ^ (i.val / 2) *
      secondSimpleReflection n

theorem firstSimpleReflection_mul_self (n : ℕ) :
    firstSimpleReflection n * firstSimpleReflection n = 1 :=
  DihedralGroup.sr_mul_self 0

theorem secondSimpleReflection_mul_self (n : ℕ) :
    secondSimpleReflection n * secondSimpleReflection n = 1 :=
  DihedralGroup.sr_mul_self 1

theorem simpleReflection_zero (n : ℕ) :
    simpleReflection n 0 = firstSimpleReflection n := by
  unfold simpleReflection
  exact ite_eq_left rfl

theorem simpleReflection_one (n : ℕ) :
    simpleReflection n 1 = secondSimpleReflection n := by
  unfold simpleReflection
  exact ite_eq_right (by decide : (1 : Fin 2) ≠ 0)

theorem simpleReflection_mul_self (n : ℕ) (i : Fin 2) :
    simpleReflection n i * simpleReflection n i = 1 := by
  unfold simpleReflection
  split_ifs
  · exact firstSimpleReflection_mul_self n
  · exact secondSimpleReflection_mul_self n

theorem rotation_eq_r_one (n : ℕ) : rotation n = DihedralGroup.r 1 := by
  simp only [rotation, firstSimpleReflection, secondSimpleReflection,
    DihedralGroup.sr_mul_sr, sub_zero]

/-- The distinguished rotation satisfies the relation of an `n`-gon. -/
theorem rotation_pow_eq_one (n : ℕ) : rotation n ^ n = 1 := by
  rw [rotation_eq_r_one]
  exact DihedralGroup.r_one_pow_n

theorem rootReflection_of_even_index {n : ℕ} (i : PositiveRootIndex n)
    (heven : i.val % 2 = 0) :
    rootReflection i = rotation n ^ (i.val / 2) * firstSimpleReflection n := by
  rw [rootReflection, ite_eq_left heven, rotation]

theorem rootReflection_of_odd_index {n : ℕ} (i : PositiveRootIndex n)
    (hodd : i.val % 2 ≠ 0) :
    rootReflection i =
      (secondSimpleReflection n * firstSimpleReflection n) ^ (i.val / 2) *
        secondSimpleReflection n := by
  rw [rootReflection, ite_eq_right hodd]

theorem rootReflection_first {n : ℕ} (hpositive : 0 < n) :
    rootReflection (⟨0, hpositive⟩ : PositiveRootIndex n) = firstSimpleReflection n := by
  rw [rootReflection_of_even_index _ (by simp)]
  rw [Fin.val_mk, Nat.zero_div, pow_zero, one_mul]

theorem rootReflection_second {n : ℕ} (htwo : 1 < n) :
    rootReflection (⟨1, htwo⟩ : PositiveRootIndex n) = secondSimpleReflection n := by
  rw [rootReflection_of_odd_index _ (by simp)]
  rw [Fin.val_mk, Nat.div_eq_of_lt (by decide : 1 < 2), pow_zero, one_mul]

/-- Every indexed root reflection is an involution. -/
theorem rootReflection_mul_self {n : ℕ} (i : PositiveRootIndex n) :
    rootReflection i * rootReflection i = 1 := by
  unfold rootReflection firstSimpleReflection secondSimpleReflection
  split_ifs <;> simp only [DihedralGroup.sr_mul_sr, DihedralGroup.r_pow,
    DihedralGroup.r_mul_sr, sub_self, DihedralGroup.r_zero]

end Schubert.Dihedral
