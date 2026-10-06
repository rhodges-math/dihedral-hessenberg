import Mathlib.RepresentationTheory.Basic
import Schubert.Dihedral.CoxeterSystem

/-! # Scalar eigenvector identities from the distinguished simple reflections -/

namespace Schubert.Dihedral

/-- Scalar eigenvector identities on the simple generators determine the whole group action. -/
theorem eigenvector_of_simple {n : ℕ} (hthree : 3 ≤ n) {K V : Type*}
    [CommRing K] [AddCommGroup V] [Module K V]
    (source : Representation K (DihedralGroup n) V) (character : DihedralGroup n →* K)
    (vector : V) (hsimple : ∀ index, source (simpleReflection n index) vector =
      character (simpleReflection n index) • vector) (element : DihedralGroup n) :
    source element vector = character element • vector := by
  apply (coxeterSystem n hthree).simple_induction_left element
  · simp
  · intro element index hinduction
    rw [coxeterSystem_simple, map_mul, Module.End.mul_apply, hinduction,
      map_smul, hsimple, map_mul, mul_smul, smul_comm]

end Schubert.Dihedral
