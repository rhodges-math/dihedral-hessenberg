import DihedralHessenberg.Dihedral.RootObjects
import DihedralHessenberg.Dihedral.RootPolynomial

/-! # Involutions and their normal forms -/

namespace Schubert.Dihedral.PositiveRoot

/-- Every positive-root reflection equals its inverse. -/
theorem reflection_inv {n : ℕ} (alpha : PositiveRoot n) :
    alpha.reflection⁻¹ = alpha.reflection :=
  inv_eq_of_mul_eq_one_left alpha.reflection_square

/-- Reflection negates the linear form of its normal vector. -/
theorem reflection_form {n : ℕ} [NeZero n] (alpha : PositiveRoot n) :
    polynomialAction n alpha.reflection alpha.form = -alpha.form := by
  change (polynomialAction n (rootReflection alpha.index)).toAlgHom
    (linearPolynomial (complexify alpha.val)) = -linearPolynomial (complexify alpha.val)
  rw [← alpha.index_val]
  change (polynomialAction n (rootReflection alpha.index)).toAlgHom
    (rootPolynomial n alpha.index) = -rootPolynomial n alpha.index
  rw [polynomialAction_rootReflection]
  exact reflection_normal_polynomial _ (complexPositiveRoot_nonisotropic n alpha.index)

end Schubert.Dihedral.PositiveRoot
