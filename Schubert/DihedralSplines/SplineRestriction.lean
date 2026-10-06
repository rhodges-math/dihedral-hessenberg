import Schubert.DihedralSplines.PaperFull
import Schubert.DihedralSplines.PaperGrading

/-! # Restricting selected reflection conditions -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} (selected larger : RootSubset n)

/-- Forget selected reflection conditions while retaining the same polynomial function. -/
def restrict (hsubset : (selected : Set RealPlane) ⊆ larger) :
    larger.Spline →ₐ[ℂ] selected.Spline where
  toFun value := ⟨value.val, fun vertex alpha hmem =>
    value.property vertex alpha (hsubset hmem)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

/-- Restriction leaves every vertex value unchanged. -/
theorem restrict_apply (hsubset : (selected : Set RealPlane) ⊆ larger)
    (value : larger.Spline) (vertex : DihedralGroup n) :
    (selected.restrict larger hsubset value : DihedralGroup n → CoordinatePolynomial) vertex =
      (value : DihedralGroup n → CoordinatePolynomial) vertex := rfl

/-- Restriction is injective because it preserves the whole polynomial-valued function. -/
theorem restrict_injective (hsubset : (selected : Set RealPlane) ⊆ larger) :
    Function.Injective (selected.restrict larger hsubset) := by
  intro first second heq
  apply Subtype.ext
  exact congrArg (fun value : selected.Spline =>
    (value : DihedralGroup n → CoordinatePolynomial)) heq

/-- Restriction preserves pointwise homogeneity. -/
theorem restrict_mem_piece (hsubset : (selected : Set RealPlane) ⊆ larger)
    (value : larger.Spline) (degree : ℕ) (hvalue : value ∈ larger.piece degree) :
    selected.restrict larger hsubset value ∈ selected.piece degree := hvalue

/-- A full geometric spline satisfies every selected positive-root condition. -/
def restrictFull : (full n).Spline →ₐ[ℂ] selected.Spline :=
  selected.restrict (full n) selected.positive

end Schubert.Dihedral.RootSubset
