import DihedralHessenberg.Dihedral.InvariantOrbitBasis
import Mathlib.RingTheory.TensorProduct.Basic

/-! Evaluation of the invariant-relative tensor algebra on group orbits. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.Dihedral

/-- Evaluation of the invariant-relative tensor algebra on group orbits. -/
def tensorEvaluation (n : ℕ) [NeZero n] :
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial →ₐ[CoordinatePolynomial]
      (DihedralGroup n → CoordinatePolynomial) :=
  AlgHom.liftEquiv (invariantSubalgebra n) CoordinatePolynomial CoordinatePolynomial
    (DihedralGroup n → CoordinatePolynomial) (AlgHom.pi (invariantAction n))

/-- A pure tensor evaluates as its first factor times the action of its second. -/
theorem tensorEvaluation_tmul (n : ℕ) [NeZero n]
    (first second : CoordinatePolynomial) (element : DihedralGroup n) :
    tensorEvaluation n (first ⊗ₜ[invariantSubalgebra n] second) element =
      first * polynomialAction n element second := rfl

/-- Orbit evaluation embeds the full invariant-relative tensor algebra. -/
theorem tensorEvaluation_injective (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.Injective (tensorEvaluation n) := by
  obtain ⟨basis, hindependent⟩ := exists_invariant_orbit_basis n hthree
  change Function.Injective
    ((LinearMap.pi fun element => (invariantAction n element).toLinearMap).liftBaseChange
      CoordinatePolynomial)
  apply (LinearMap.liftBaseChange_injective_iff _ basis).mpr
  exact hindependent

end Schubert.Dihedral
