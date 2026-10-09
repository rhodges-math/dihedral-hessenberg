import DihedralHessenberg.Paper.BoundaryForm

/-! # Dot translation of explicit localized splines -/

noncomputable section

namespace Schubert.DihedralSplines.BoundaryForm

open Schubert.Dihedral
open scoped Classical

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}
variable {vertex : DihedralGroup n} {value : ideal.toRootSubset.Spline}

/-- Dot translation preserves the displayed boundary formula whenever its upper support is known. -/
def ofDot (form : BoundaryForm ideal vertex value) (element next : DihedralGroup n)
    (hnext : element * vertex = next)
    (hsupport : ∀ current, ¬BruhatLE n hthree next current →
      (ideal.toRootSubset.dot hthree element value :
        DihedralGroup n → CoordinatePolynomial) current = 0) :
    BoundaryForm ideal next (ideal.toRootSubset.dot hthree element value) := by
  refine ⟨(fun current => element * current) '' form.vertices,
    ⟨vertex, form.base_mem, hnext⟩, ?_,
    (fun current => form.coefficient (element⁻¹ * current)), ?_, ?_⟩
  · rintro current ⟨original, horiginal, rfl⟩
    by_contra hnot
    have hnonzero := (ideal.toRootSubset.dot_support hthree element original value).mpr
      ((form.support_exact original).mpr horiginal)
    exact hnonzero (hsupport _ hnot)
  · rintro current ⟨original, horiginal, rfl⟩
    simpa only [inv_mul_cancel_left] using form.coefficient_ne original horiginal
  · intro current
    by_cases hcurrent : current ∈ (fun original => element * original) '' form.vertices
    · rw [ite_eq_left hcurrent]
      obtain ⟨original, horiginal, rfl⟩ := hcurrent
      simp only [inv_mul_cancel_left]
      apply ideal.toRootSubset.dot_localized hthree form.vertices element original value
      rw [form.formula, ite_eq_left horiginal]
    · have houtside : element⁻¹ * current ∉ form.vertices := by
        intro hinside
        exact hcurrent ⟨element⁻¹ * current, hinside, mul_inv_cancel_left _ _⟩
      rw [ite_eq_right hcurrent, ideal.toRootSubset.dot_apply, form.formula,
        ite_eq_right houtside, map_zero]

end Schubert.DihedralSplines.BoundaryForm
