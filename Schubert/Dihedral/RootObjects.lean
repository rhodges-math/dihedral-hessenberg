import Schubert.Dihedral.RootGeometry
import Schubert.Dihedral.RootReflectionAction
import Schubert.Dihedral.RootPreservation

/-! # Positive root vectors and the signed root action -/

noncomputable section

namespace Schubert.Dihedral

/-- A positive unit root vector. -/
abbrev PositiveRoot (n : ℕ) := {alpha : RealPlane // alpha ∈ positiveRoots n}

/-- A unit root vector of either sign. -/
abbrev Root (n : ℕ) := {alpha : RealPlane // alpha ∈ roots n}

/-- Alternating numbering identifies the positive root vectors with finite indices. -/
def positiveRootEquiv (n : ℕ) : PositiveRootIndex n ≃ PositiveRoot n :=
  Equiv.ofBijective (fun index => ⟨positiveRoot n index, ⟨index, rfl⟩⟩) (by
    constructor
    · intro first second heq
      exact positiveRoot_injective n (congrArg Subtype.val heq)
    · intro alpha
      obtain ⟨index, hindex⟩ := alpha.property
      exact ⟨index, Subtype.ext hindex⟩)

/-- The numbered positive root is its real vector. -/
@[simp] theorem positiveRootEquiv_val (n : ℕ) (index : PositiveRootIndex n) :
    (positiveRootEquiv n index).val = positiveRoot n index := rfl

namespace PositiveRoot

/-- The alternating index of a positive root vector. -/
def index {n : ℕ} (alpha : PositiveRoot n) : PositiveRootIndex n :=
  (positiveRootEquiv n).symm alpha

/-- Recovering a positive root from its alternating index returns the vector. -/
@[simp] theorem index_val {n : ℕ} (alpha : PositiveRoot n) :
    positiveRoot n alpha.index = alpha.val :=
  congrArg Subtype.val ((positiveRootEquiv n).apply_symm_apply alpha)

/-- Index recovery is inverse to alternating numbering. -/
@[simp] theorem index_equiv (n : ℕ) (index : PositiveRootIndex n) :
    (positiveRootEquiv n index).index = index :=
  (positiveRootEquiv n).symm_apply_apply index

/-- The group reflection in a positive root vector. -/
def reflection {n : ℕ} (alpha : PositiveRoot n) : DihedralGroup n :=
  rootReflection alpha.index

/-- The linear form associated with a positive root vector. -/
def form {n : ℕ} (alpha : PositiveRoot n) : CoordinatePolynomial :=
  linearPolynomial (complexify alpha.val)

/-- Alternating numbering preserves group reflections. -/
@[simp] theorem reflection_equiv (n : ℕ) (index : PositiveRootIndex n) :
    (positiveRootEquiv n index).reflection = rootReflection index := by
  rw [reflection, index_equiv]

/-- Alternating numbering preserves root linear forms. -/
@[simp] theorem form_equiv (n : ℕ) (index : PositiveRootIndex n) :
    (positiveRootEquiv n index).form = rootPolynomial n index := rfl

/-- A positive root vector is uniquely determined by its group reflection. -/
theorem reflection_injective (n : ℕ) :
    Function.Injective (reflection (n := n)) := by
  intro first second heq
  have hindex := rootReflection_injective n heq
  exact (positiveRootEquiv n).symm.injective hindex

/-- The group reflection acts by the normal reflection of its vector. -/
theorem reflection_operator {n : ℕ} (alpha : PositiveRoot n) :
    vectorOperator n alpha.reflection = complexReflection (complexify alpha.val) := by
  rw [reflection, vectorOperator_rootReflection]
  change complexReflection (complexify (positiveRoot n alpha.index)) = _
  rw [index_val]

/-- Every positive root reflection is an involution. -/
theorem reflection_square {n : ℕ} (alpha : PositiveRoot n) :
    alpha.reflection * alpha.reflection = 1 := rootReflection_mul_self alpha.index

end PositiveRoot

/-- The real coordinates of the action on the complexification of a real vector. -/
def realAction (n : ℕ) (element : DihedralGroup n) (alpha : RealPlane) : RealPlane :=
  fun coordinate => (vectorOperator n element (complexify alpha) coordinate).re

/-- The action on a root agrees with complexification of its real coordinates. -/
theorem realAction_complexify (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (alpha : RealPlane) (hroot : alpha ∈ roots n) :
    complexify (realAction n element alpha) = vectorOperator n element (complexify alpha) := by
  obtain ⟨image, _, heq⟩ := vectorOperator_complexify_mem_roots n element alpha hroot
  change complexify (fun coordinate =>
    (vectorOperator n element (complexify alpha) coordinate).re) = _
  simp only [heq, complexify, Complex.ofReal_re]

/-- The real coordinate action preserves the signed root set. -/
theorem realAction_mem (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (alpha : RealPlane) (hroot : alpha ∈ roots n) : realAction n element alpha ∈ roots n :=
  vectorOperator_realRootImage_mem_roots n element alpha hroot

/-- The identity fixes every real vector. -/
theorem realAction_one (n : ℕ) : realAction n 1 = id := by
  funext alpha coordinate
  simp only [realAction, vectorOperator_one, LinearMap.id_apply, complexify, Complex.ofReal_re]
  rfl

/-- Multiplication composes the real action on signed roots. -/
theorem realAction_mul (n : ℕ) [NeZero n] (first second : DihedralGroup n)
    (alpha : RealPlane) (hroot : alpha ∈ roots n) :
    realAction n (first * second) alpha = realAction n first (realAction n second alpha) := by
  have heq : complexify (realAction n (first * second) alpha) =
      complexify (realAction n first (realAction n second alpha)) := by
    rw [realAction_complexify n (first * second) alpha hroot,
      realAction_complexify n first _ (realAction_mem n second alpha hroot),
      realAction_complexify n second alpha hroot, vectorOperator_mul, LinearMap.comp_apply]
  funext coordinate
  exact Complex.ofReal_injective (congrFun heq coordinate)

namespace Root

/-- The signed root obtained by acting on a root vector. -/
def action {n : ℕ} [NeZero n] (element : DihedralGroup n) (alpha : Root n) : Root n :=
  ⟨realAction n element alpha.val, realAction_mem n element alpha.val alpha.property⟩

/-- The group action on the full signed root carrier. -/
instance mulAction (n : ℕ) [NeZero n] : MulAction (DihedralGroup n) (Root n) where
  smul := action
  one_smul alpha := Subtype.ext (congrFun (realAction_one n) alpha.val)
  mul_smul first second alpha := Subtype.ext (realAction_mul n first second _ alpha.property)

end Root

end Schubert.Dihedral
