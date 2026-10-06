import Schubert.DihedralSplines.BoundaryTranslation
import Schubert.DihedralSplines.UpperLocalization

/-! # Explicit localized flow-up functions -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral
open scoped Classical

/-- A spline with the displayed nonzero boundary-product formula on an upper-supported subset. -/
structure BoundaryForm {n : ℕ} {hthree : 3 ≤ n} [NeZero n]
    (ideal : HessenbergIdeal n hthree) (vertex : DihedralGroup n)
    (value : ideal.toRootSubset.Spline) where
  /-- The vertex subset of the support. -/
  vertices : Set (DihedralGroup n)
  /-- The indexing vertex belongs to the support subset. -/
  base_mem : vertex ∈ vertices
  /-- The support subset lies in the indexing vertex's Bruhat upper ideal. -/
  upper : ∀ current ∈ vertices, BruhatLE n hthree vertex current
  /-- The coefficient function in the boundary-product formula. -/
  coefficient : DihedralGroup n → ℂ
  /-- All coefficients on the support subset are nonzero. -/
  coefficient_ne : ∀ current ∈ vertices, coefficient current ≠ 0
  /-- The exact displayed geometric boundary-product formula and zero outside. -/
  formula : ∀ current, (value : DihedralGroup n → CoordinatePolynomial) current =
    if current ∈ vertices then MvPolynomial.C (coefficient current) *
      ideal.toRootSubset.boundaryProduct vertices current else 0

namespace BoundaryForm

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] {ideal : HessenbergIdeal n hthree}
variable {vertex : DihedralGroup n} {value : ideal.toRootSubset.Spline}

/-- A localized formula has exactly its specified support subset. -/
theorem support_exact (form : BoundaryForm ideal vertex value) (current : DihedralGroup n) :
    (value : DihedralGroup n → CoordinatePolynomial) current ≠ 0 ↔ current ∈ form.vertices := by
  rw [form.formula]
  by_cases hcurrent : current ∈ form.vertices
  · rw [ite_eq_left hcurrent]
    exact iff_of_true (mul_ne_zero (MvPolynomial.C_ne_zero.mpr
      (form.coefficient_ne current hcurrent))
      (ideal.toRootSubset.boundaryProduct_ne_zero form.vertices current)) hcurrent
  · rw [ite_eq_right hcurrent]
    exact iff_of_false (not_not_intro rfl) hcurrent

/-- Any supported boundary-degree spline with nonzero diagonal yields the displayed formula. -/
def ofUpper (upper : HessenbergIdeal.Upper ideal)
    (value : ideal.toRootSubset.Spline)
    (hhomogeneous : value ∈ ideal.toRootSubset.piece
      (ideal.toRootSubset.length upper.minimum))
    (hsupport : ∀ current, ¬BruhatLE n hthree upper.minimum current →
      (value : DihedralGroup n → CoordinatePolynomial) current = 0)
    (hbase : (value : DihedralGroup n → CoordinatePolynomial) upper.minimum ≠ 0) :
    BoundaryForm ideal upper.minimum value := by
  classical
  let coefficient : DihedralGroup n → ℂ := fun current =>
    if hcurrent : BruhatLE n hthree upper.minimum current then
      Classical.choose (upper.localized value hhomogeneous hsupport hbase current hcurrent)
    else 0
  refine ⟨{current | BruhatLE n hthree upper.minimum current},
    bruhatLE_refl n hthree _, (fun _ h => h), coefficient, ?_, ?_⟩
  · intro current hcurrent
    change BruhatLE n hthree upper.minimum current at hcurrent
    dsimp only [coefficient]
    rw [dite_eq_left hcurrent]
    exact (Classical.choose_spec
      (upper.localized value hhomogeneous hsupport hbase current hcurrent)).1
  · intro current
    simp only [Set.mem_ofPred_eq]
    by_cases hcurrent : BruhatLE n hthree upper.minimum current
    · rw [ite_eq_left hcurrent]
      dsimp only [coefficient]
      rw [dite_eq_left hcurrent]
      exact (Classical.choose_spec
        (upper.localized value hhomogeneous hsupport hbase current hcurrent)).2
    · rw [ite_eq_right hcurrent]
      exact hsupport current hcurrent

end BoundaryForm

end Schubert.DihedralSplines
