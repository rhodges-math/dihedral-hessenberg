import Schubert.DihedralSplines.PaperLocalization

/-! # Translation of geometric boundary products -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected : RootSubset n)

omit [NeZero n] in
/-- Left translation preserves the selected boundary roots of corresponding vertices. -/
theorem boundaryRoots_translate (vertices : Set (DihedralGroup n))
    (translate vertex : DihedralGroup n) :
    selected.boundaryRoots ((fun current => translate * current) '' vertices)
      (translate * vertex) = selected.boundaryRoots vertices vertex := by
  classical
  ext alpha
  rw [selected.mem_boundaryRoots, selected.mem_boundaryRoots]
  have hmem : (translate * vertex) * alpha.reflection ∈
      (fun current => translate * current) '' vertices ↔ vertex * alpha.reflection ∈ vertices := by
    constructor
    · rintro ⟨current, hcurrent, heq⟩
      have hcancel : current = vertex * alpha.reflection :=
        mul_left_cancel (by simpa only [mul_assoc] using heq)
      exact hcancel ▸ hcurrent
    · intro hcurrent
      exact ⟨vertex * alpha.reflection, hcurrent, (mul_assoc _ _ _).symm⟩
  exact and_congr_right fun _ => not_congr hmem

/-- The boundary product of a translated subset is the polynomial action of its original. -/
theorem boundaryProduct_translate (vertices : Set (DihedralGroup n))
    (translate vertex : DihedralGroup n) :
    selected.boundaryProduct ((fun current => translate * current) '' vertices)
      (translate * vertex) =
        polynomialAction n translate (selected.boundaryProduct vertices vertex) :=
  by
  unfold boundaryProduct
  rw [selected.boundaryRoots_translate, map_prod]
  apply Finset.prod_congr rfl
  intro alpha _
  rw [← PositiveRoot.action_form, ← PositiveRoot.action_form]
  rw [map_mul]
  rfl

/-- Dot translation preserves the nonzero support at corresponding vertices. -/
theorem dot_support (hthree : 3 ≤ n) (translate vertex : DihedralGroup n)
    (value : selected.Spline) :
    (selected.dot hthree translate value : DihedralGroup n → CoordinatePolynomial)
      (translate * vertex) ≠ 0 ↔
        (value : DihedralGroup n → CoordinatePolynomial) vertex ≠ 0 := by
  rw [selected.dot_apply]
  simp only [inv_mul_cancel_left]
  constructor
  · intro hnonzero hzero
    exact hnonzero (by rw [hzero, map_zero])
  · intro hnonzero hzero
    apply hnonzero
    apply (polynomialAction n translate).injective
    simpa only [map_zero] using hzero

/-- Dot translation preserves the exact scalar in a boundary-product formula. -/
theorem dot_localized (hthree : 3 ≤ n) (vertices : Set (DihedralGroup n))
    (translate vertex : DihedralGroup n) (value : selected.Spline) (scalar : ℂ)
    (hvalue : (value : DihedralGroup n → CoordinatePolynomial) vertex =
      MvPolynomial.C scalar * selected.boundaryProduct vertices vertex) :
    (selected.dot hthree translate value : DihedralGroup n → CoordinatePolynomial)
      (translate * vertex) = MvPolynomial.C scalar *
        selected.boundaryProduct ((fun current => translate * current) '' vertices)
          (translate * vertex) := by
  have hconstant : polynomialAction n translate (MvPolynomial.C scalar) =
      MvPolynomial.C scalar := by
    simpa only [MvPolynomial.algebraMap_eq] using (polynomialAction n translate).commutes scalar
  rw [selected.dot_apply, inv_mul_cancel_left, hvalue, map_mul, hconstant,
    selected.boundaryProduct_translate]

end Schubert.Dihedral.RootSubset
