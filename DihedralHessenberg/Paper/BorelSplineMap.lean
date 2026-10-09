import DihedralHessenberg.Dihedral.InvariantTensorEvaluation
import DihedralHessenberg.Paper.PaperFull
import DihedralHessenberg.Paper.PaperAction

/-! Invariant-relative tensor evaluation satisfies every geometric spline condition. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- Invariant-relative tensor evaluation satisfies every geometric spline condition. -/
theorem tensorEvaluation_spline (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (value : CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :
    (RootSubset.full n).IsSpline (tensorEvaluation n value) := by
  change tensorEvaluation n value ∈ (RootSubset.full n).splineAlgebra
  induction value using TensorProduct.inductionOn with
  | tmul first second =>
      exact ((RootSubset.full n).constantHom hthree first *
        (RootSubset.full n).orbitHom hthree second).property
  | add first second hfirst hsecond =>
      simpa using (RootSubset.full n).splineAlgebra.add_mem hfirst hsecond

/-- The invariant-relative tensor map into the full geometric spline algebra. -/
def borelHom (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    letI := (RootSubset.full n).leftAlgebra hthree
    CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial →ₐ[CoordinatePolynomial]
      (RootSubset.full n).Spline := by
  letI := (RootSubset.full n).leftAlgebra hthree
  exact
    { toFun := fun value => ⟨tensorEvaluation n value, tensorEvaluation_spline n hthree value⟩
      map_zero' := Subtype.ext (map_zero (tensorEvaluation n))
      map_one' := Subtype.ext (map_one (tensorEvaluation n))
      map_add' := fun first second => Subtype.ext (map_add (tensorEvaluation n) first second)
      map_mul' := fun first second => Subtype.ext (map_mul (tensorEvaluation n) first second)
      commutes' := fun scalar => Subtype.ext ((tensorEvaluation n).commutes scalar) }

/-- The Borel map retains pure-tensor values at every group vertex. -/
theorem borelHom_tmul (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (first second : CoordinatePolynomial) (element : DihedralGroup n) :
    (borelHom n hthree (first ⊗ₜ[invariantSubalgebra n] second)).val element =
      first * polynomialAction n element second := rfl

/-- The Borel tensor map is injective before any dimension or surjectivity argument. -/
theorem borelHom_injective (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Function.Injective (borelHom n hthree) := by
  intro first second heq
  exact tensorEvaluation_injective n hthree (congrArg Subtype.val heq)

end Schubert.DihedralSplines
