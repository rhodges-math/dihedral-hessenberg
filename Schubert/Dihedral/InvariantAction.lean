import Schubert.Dihedral.FaithfulRealization
import Schubert.Dihedral.Invariants
import Schubert.Dihedral.RootPolynomial

/-! The polynomial action is faithful. -/

noncomputable section
namespace Schubert.Dihedral

/-- The polynomial action is faithful. -/
theorem polynomialAction_injective (n : ℕ) [NeZero n] :
    Function.Injective (polynomialAction n) := by
  intro first second heq
  apply vectorOperator_injective n
  apply LinearMap.ext
  intro vector
  apply linearPolynomial_injective
  rw [← polynomialAction_linearPolynomial, ← polynomialAction_linearPolynomial, heq]

/-- Each polynomial action map is linear over the fixed invariant algebra. -/
def invariantAction (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    CoordinatePolynomial →ₐ[invariantSubalgebra n] CoordinatePolynomial where
  __ := (polynomialAction n element).toRingHom
  commutes' invariant := (mem_invariantSubalgebra n invariant.val).mp invariant.property element

/-- The invariant-linear action retains the polynomial values. -/
theorem invariantAction_apply (n : ℕ) [NeZero n] (element : DihedralGroup n)
    (polynomial : CoordinatePolynomial) :
    invariantAction n element polynomial = polynomialAction n element polynomial := rfl

/-- The distinct group elements induce distinct invariant-linear algebra maps. -/
theorem invariantAction_injective (n : ℕ) [NeZero n] :
    Function.Injective (invariantAction n) := by
  intro first second heq
  apply polynomialAction_injective n
  apply AlgEquiv.ext
  intro polynomial
  exact DFunLike.congr_fun heq polynomial

end Schubert.Dihedral
