import Mathlib.LinearAlgebra.Eigenspace.Basic
import DihedralHessenberg.Dihedral.InvariantCoefficients

/-! # Separation of rotation eigencomponents

Powers of the primitive rotation eigenvalue give distinct eigenspaces. A vanishing
sum of components in those eigenspaces has every component equal to zero.
-/

noncomputable section

namespace Schubert.Dihedral

/-- The powers indexed by Fin n of the primitive rotation eigenvalue are distinct. -/
theorem rotationEigenvalue_pow_injective (n : ℕ) [NeZero n] :
    Function.Injective (fun index : Fin n =>
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val) := by
  intro first second hequal
  apply Fin.ext
  exact (isPrimitiveRoot_exp_rotation_angle n).pow_inj first.isLt second.isLt hequal

/-- A vanishing sum of distinct rotation eigencomponents has all its components zero. -/
theorem rotation_eigencomponents_eq_zero (n : ℕ) [NeZero n]
    (components : Fin n → CoordinatePolynomial)
    (heigen : ∀ index, polynomialAction n (rotation n) (components index) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val • components index)
    (hsum : ∑ index, components index = 0) : ∀ index, components index = 0 := by
  let operator : Module.End ℂ CoordinatePolynomial :=
    (polynomialAction n (rotation n)).toLinearMap
  have hindependent := operator.eigenspaces_iSupIndep.comp (rotationEigenvalue_pow_injective n)
  have hcomponents : ∀ index ∈ (Finset.univ : Finset (Fin n)),
      components index ∈ operator.eigenspace
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n) ^ index.val) := by
    intro index _
    exact Module.End.mem_eigenspace_iff.mpr (heigen index)
  exact fun index => (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mp hindependent
    Finset.univ components hcomponents hsum index (Finset.mem_univ index)

end Schubert.Dihedral
