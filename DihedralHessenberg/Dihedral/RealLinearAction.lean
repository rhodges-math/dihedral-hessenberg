import DihedralHessenberg.Dihedral.UnitDirections
import DihedralHessenberg.Dihedral.RootGenerators
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # The faithful real-plane linear action -/

noncomputable section

namespace Schubert.Dihedral

/-- The real coordinate action as a real linear automorphism. -/
def realLinearEquiv (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    RealPlane ≃ₗ[ℝ] RealPlane where
  toFun := realAction n element
  invFun := realAction n element⁻¹
  left_inv vector := by
    rw [← realAction_mul_plane, inv_mul_cancel, realAction_one]
    rfl
  right_inv vector := by
    rw [← realAction_mul_plane, mul_inv_cancel, realAction_one]
    rfl
  map_add' first second := by
    have hcomplex : complexify (first + second) = complexify first + complexify second := by
      funext coordinate
      simp only [complexify, Pi.add_apply, Complex.ofReal_add]
    funext coordinate
    unfold realAction
    rw [hcomplex, map_add]
    simp only [Pi.add_apply, Complex.add_re]
  map_smul' scalar vector := realAction_smul_plane n element scalar vector

/-- The dihedral group homomorphism into real-plane linear automorphisms. -/
def realLinearAction (n : ℕ) [NeZero n] : DihedralGroup n →* (RealPlane ≃ₗ[ℝ] RealPlane) where
  toFun := realLinearEquiv n
  map_one' := by
    ext vector coordinate
    exact congrFun (congrFun (realAction_one n) vector) coordinate
  map_mul' first second := by
    ext vector coordinate
    exact congrFun (realAction_mul_plane n first second vector) coordinate

/-- Packaging the real action as a linear automorphism preserves every value. -/
@[simp] theorem realLinearAction_apply (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (vector : RealPlane) : realLinearAction n element vector = realAction n element vector := rfl

/-- The real linear action is faithful. -/
theorem realLinearAction_injective (n : ℕ) [NeZero n] :
    Function.Injective (realLinearAction n) := by
  intro first second heq
  apply realAction_injective n
  funext vector
  exact congrArg (fun operator : RealPlane ≃ₗ[ℝ] RealPlane => operator vector) heq

end Schubert.Dihedral
