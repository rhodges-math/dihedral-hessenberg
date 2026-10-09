import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic

/-! # Bilinear multiplication on homogeneous submodules -/

namespace Schubert.Splines

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Ring multiplication restricted to homogeneous submodules and its total degree. -/
def gradedMultiplication (pieces : ℕ → Submodule K A)
    (hmul : ∀ first second (left : A) (right : A),
      left ∈ pieces first → right ∈ pieces second → left * right ∈ pieces (first + second))
    (first second : ℕ) : pieces first →ₗ[K] pieces second →ₗ[K] pieces (first + second) where
  toFun left :=
    { toFun := fun right => ⟨left.val * right.val,
        hmul first second left.val right.val left.property right.property⟩
      map_add' := fun right another => Subtype.ext (mul_add left.val right.val another.val)
      map_smul' := fun scalar right => Subtype.ext (mul_smul_comm scalar left.val right.val) }
  map_add' left another := by
    ext right
    exact add_mul left.val another.val right.val
  map_smul' scalar left := by
    ext right
    exact smul_mul_assoc scalar left.val right.val

/-- The homogeneous bilinear map retains ring multiplication. -/
theorem gradedMultiplication_apply (pieces : ℕ → Submodule K A)
    (hmul : ∀ first second (left : A) (right : A),
      left ∈ pieces first → right ∈ pieces second → left * right ∈ pieces (first + second))
    (first second : ℕ) (left : pieces first) (right : pieces second) :
    (gradedMultiplication pieces hmul first second left right : A) = left.val * right.val := rfl

end Schubert.Splines
