import DihedralHessenberg.Paper.PaperQuotientAction
import DihedralHessenberg.Splines.GradedMultiplication

/-! # Homogeneous multiplication in the two geometric quotients -/

noncomputable section
namespace Schubert.Dihedral.RootSubset
open Schubert.DihedralSplines Schubert.Splines

variable {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)

namespace Left

/-- Homogeneous quotient degrees add under multiplication. -/
theorem piece_mul (first second : ℕ) (left right : Quotient selected hthree)
    (hleft : left ∈ piece selected hthree first)
    (hright : right ∈ piece selected hthree second) :
    left * right ∈ piece selected hthree (first + second) := by
  obtain ⟨firstValue, hfirst, rfl⟩ := (mem_piece selected hthree first left).mp hleft
  obtain ⟨secondValue, hsecond, rfl⟩ := (mem_piece selected hthree second right).mp hright
  rw [← map_mul]
  exact (mem_piece selected hthree _ _).mpr ⟨firstValue * secondValue,
    fun vertex => (hfirst vertex).mul (hsecond vertex), rfl⟩

/-- The left quotient multiplication is a bilinear map on ordinary degree pieces. -/
def multiplication (first second : ℕ) :
    piece selected hthree first →ₗ[ℂ] piece selected hthree second →ₗ[ℂ]
      piece selected hthree (first + second) :=
  gradedMultiplication (K := ℂ) (A := Quotient selected hthree)
    (piece selected hthree) (piece_mul selected hthree) first second

/-- Homogeneous multiplication preserves the quotient product. -/
theorem multiplication_apply (first second : ℕ)
    (left : piece selected hthree first) (right : piece selected hthree second) :
    (multiplication selected hthree first second left right : Quotient selected hthree) =
      left.val * right.val := rfl

/-- Left quotient multiplication commutes with the diagonal dot action. -/
theorem multiplication_dot (first second : ℕ) (element : DihedralGroup n)
    (left : piece selected hthree first) (right : piece selected hthree second) :
    (multiplication selected hthree first second
      (pieceRepresentation selected hthree first element left)
      (pieceRepresentation selected hthree second element right) : Quotient selected hthree) =
    dotEquiv selected hthree element (multiplication selected hthree first second left right) := by
  change dotEquiv selected hthree element left.val * dotEquiv selected hthree element right.val =
    dotEquiv selected hthree element (left.val * right.val)
  exact ((dotEquiv selected hthree element).map_mul left.val right.val).symm

end Left
namespace Right

/-- Homogeneous quotient degrees add under multiplication. -/
theorem piece_mul (first second : ℕ) (left right : Quotient selected hthree)
    (hleft : left ∈ piece selected hthree first)
    (hright : right ∈ piece selected hthree second) :
    left * right ∈ piece selected hthree (first + second) := by
  obtain ⟨firstValue, hfirst, rfl⟩ := (mem_piece selected hthree first left).mp hleft
  obtain ⟨secondValue, hsecond, rfl⟩ := (mem_piece selected hthree second right).mp hright
  rw [← map_mul]
  exact (mem_piece selected hthree _ _).mpr ⟨firstValue * secondValue,
    fun vertex => (hfirst vertex).mul (hsecond vertex), rfl⟩

/-- The right quotient multiplication is a bilinear map on ordinary degree pieces. -/
def multiplication (first second : ℕ) :
    piece selected hthree first →ₗ[ℂ] piece selected hthree second →ₗ[ℂ]
      piece selected hthree (first + second) :=
  gradedMultiplication (K := ℂ) (A := Quotient selected hthree)
    (piece selected hthree) (piece_mul selected hthree) first second

/-- Homogeneous multiplication preserves the quotient product. -/
theorem multiplication_apply (first second : ℕ)
    (left : piece selected hthree first) (right : piece selected hthree second) :
    (multiplication selected hthree first second left right : Quotient selected hthree) =
      left.val * right.val := rfl

/-- Right quotient multiplication commutes with the diagonal dot action. -/
theorem multiplication_dot (first second : ℕ) (element : DihedralGroup n)
    (left : piece selected hthree first) (right : piece selected hthree second) :
    (multiplication selected hthree first second
      (pieceRepresentation selected hthree first element left)
      (pieceRepresentation selected hthree second element right) : Quotient selected hthree) =
    dotEquiv selected hthree element (multiplication selected hthree first second left right) := by
  change dotEquiv selected hthree element left.val * dotEquiv selected hthree element right.val =
    dotEquiv selected hthree element (left.val * right.val)
  exact ((dotEquiv selected hthree element).map_mul left.val right.val).symm

end Right
end Schubert.Dihedral.RootSubset
