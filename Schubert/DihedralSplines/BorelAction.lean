import Schubert.DihedralSplines.BorelEquivalence
import Mathlib.RingTheory.TensorProduct.Maps

/-! Dot translation changes only the first factor in Borel pure tensors. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

/-- Dot translation changes only the first factor in Borel pure tensors. -/
theorem borelEquiv_dot_tmul (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (element : DihedralGroup n) (first second : CoordinatePolynomial) :
    (RootSubset.full n).dot hthree element
      (borelEquiv n hthree (first ⊗ₜ[invariantSubalgebra n] second)) =
      borelEquiv n hthree
        (polynomialAction n element first ⊗ₜ[invariantSubalgebra n] second) := by
  let := (RootSubset.full n).leftAlgebra hthree
  apply Subtype.ext
  funext vertex
  change polynomialAction n element
    ((borelEquiv n hthree (first ⊗ₜ[invariantSubalgebra n] second)).val
      (element⁻¹ * vertex)) = _
  rw [borelEquiv_tmul, borelEquiv_tmul]
  have haction := congrArg (fun action : CoordinatePolynomial ≃ₐ[ℂ] CoordinatePolynomial =>
    action second) ((polynomialAction n).map_mul element (element⁻¹ * vertex))
  have hcompose : polynomialAction n element
      (polynomialAction n (element⁻¹ * vertex) second) = polynomialAction n vertex second := by
    simpa only [AlgEquiv.mul_apply, mul_inv_cancel_left] using haction.symm
  exact (map_mul (polynomialAction n element) first
    (polynomialAction n (element⁻¹ * vertex) second)).trans
      (congrArg (fun value => polynomialAction n element first * value) hcompose)

/-- The dot action is the standard first-factor algebra action on every tensor. -/
theorem borelEquiv_dot (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (element : DihedralGroup n)
    (value : CoordinatePolynomial ⊗[invariantSubalgebra n] CoordinatePolynomial) :
    (RootSubset.full n).dot hthree element (borelEquiv n hthree value) =
      borelEquiv n hthree
        (Algebra.TensorProduct.map (invariantAction n element)
          (AlgHom.id (invariantSubalgebra n) CoordinatePolynomial) value) := by
  induction value using TensorProduct.inductionOn with
  | tmul first second =>
      rw [Algebra.TensorProduct.map_tmul]
      exact borelEquiv_dot_tmul n hthree element first second
  | add first second hfirst hsecond =>
      let := (RootSubset.full n).leftAlgebra hthree
      change (RootSubset.full n).dotEquiv hthree element
        ((borelEquiv n hthree) (first + second)) = _
      simp only [map_add]
      change (RootSubset.full n).dot hthree element ((borelEquiv n hthree) first) +
        (RootSubset.full n).dot hthree element ((borelEquiv n hthree) second) = _
      rw [hfirst, hsecond]

end Schubert.DihedralSplines
