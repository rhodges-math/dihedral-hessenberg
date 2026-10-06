import Schubert.DihedralSplines.BorelEquivalence

/-! The first left coordinate is the first tensor variable. -/

noncomputable section
open scoped TensorProduct
namespace Schubert.DihedralSplines
open Schubert.Dihedral

private theorem left_coordinate (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (coordinate : Fin 2) :
    borelEquiv n hthree (MvPolynomial.X coordinate ⊗ₜ[invariantSubalgebra n] 1) =
      (RootSubset.full n).leftCoordinate hthree coordinate := by
  apply Subtype.ext
  funext vertex
  rw [borelEquiv_tmul]
  change MvPolynomial.X coordinate * polynomialAction n vertex 1 = MvPolynomial.X coordinate
  simp

private theorem right_coordinate (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (coordinate : Fin 2) :
    borelEquiv n hthree (1 ⊗ₜ[invariantSubalgebra n] MvPolynomial.X coordinate) =
      (RootSubset.full n).rightCoordinate hthree coordinate := by
  apply Subtype.ext
  funext vertex
  rw [borelEquiv_tmul]
  rw [one_mul]
  rfl

/-- The first left coordinate is the first tensor variable. -/
theorem borelEquiv_xLeft (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    borelEquiv n hthree (MvPolynomial.X 0 ⊗ₜ[invariantSubalgebra n] 1) =
      (RootSubset.full n).xLeft hthree := left_coordinate n hthree 0

/-- The second left coordinate is the second tensor variable. -/
theorem borelEquiv_yLeft (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    borelEquiv n hthree (MvPolynomial.X 1 ⊗ₜ[invariantSubalgebra n] 1) =
      (RootSubset.full n).yLeft hthree := left_coordinate n hthree 1

/-- The first right coordinate is the first variable in the second tensor factor. -/
theorem borelEquiv_xRight (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    borelEquiv n hthree (1 ⊗ₜ[invariantSubalgebra n] MvPolynomial.X 0) =
      (RootSubset.full n).xRight hthree := right_coordinate n hthree 0

/-- The second right coordinate is the second variable in the second tensor factor. -/
theorem borelEquiv_yRight (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    borelEquiv n hthree (1 ⊗ₜ[invariantSubalgebra n] MvPolynomial.X 1) =
      (RootSubset.full n).yRight hthree := right_coordinate n hthree 1

end Schubert.DihedralSplines
