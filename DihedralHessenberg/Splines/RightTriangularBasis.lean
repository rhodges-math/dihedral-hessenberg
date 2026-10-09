import DihedralHessenberg.Splines.Untwist
import DihedralHessenberg.Splines.TriangularBasis

/-! # Right scalar triangular spline bases

Untwisting carries a reflection spline family to a constant-label graph. Ordinary
triangular elimination there proves the basis statement for orbit scalars, with the
same support, nonzero diagonal and residual-divisibility hypotheses.
-/

namespace Schubert.Splines.ReflectionGraphData

universe u v w z

variable {K : Type u} {S : Type v} {W : Type w} {T : Type z}
variable [CommRing K] [CommRing S] [Algebra K S] [Group W]
variable [PartialOrder W]
variable (data : ReflectionGraphData K S W T) (selected : Set T)
variable (family : W → data.Spline selected)
variable (hsupport : ∀ first second, ¬ first ≤ second → (family first : W → S) second = 0)
variable (hdiagonal : ∀ vertex, (family vertex : W → S) vertex ≠ 0)
variable (hdivides : ∀ (value : data.Spline selected) vertex,
  (∀ lower, lower < vertex → (value : W → S) lower = 0) →
    (family vertex : W → S) vertex ∣ (value : W → S) vertex)

include hsupport in
/-- Triangular support is preserved by inverse vertex action. -/
theorem untwist_family_support (first second : W) (hnot : ¬ first ≤ second) :
    (data.untwistEquiv selected (family first) : W → S) second = 0 := by
  rw [data.untwistEquiv_apply, hsupport first second hnot, map_zero]

omit [PartialOrder W] in
include hdiagonal in
/-- Nonzero diagonal values remain nonzero under inverse vertex action. -/
theorem untwist_family_diagonal (vertex : W) :
    (data.untwistEquiv selected (family vertex) : W → S) vertex ≠ 0 := by
  intro hzero
  apply hdiagonal vertex
  apply (data.action vertex⁻¹).injective
  simpa only [untwistEquiv_apply, map_zero] using hzero

include hdivides in
/-- Residual divisibility transfers to the constant-label graph. -/
theorem untwist_family_divides (value : (data.fixedLabelGraph selected).Spline) (vertex : W)
    (hzero : ∀ lower, lower < vertex → (value : W → S) lower = 0) :
    (data.untwistEquiv selected (family vertex) : W → S) vertex ∣
      (value : W → S) vertex := by
  have htwistZero : ∀ lower, lower < vertex →
      ((data.untwistEquiv selected).symm value : W → S) lower = 0 := by
    intro lower hlower
    change data.action lower ((value : W → S) lower) = 0
    rw [hzero lower hlower, map_zero]
  have hdivisor := hdivides ((data.untwistEquiv selected).symm value) vertex htwistZero
  have hmapped := map_dvd (data.action vertex⁻¹).toRingHom hdivisor
  change data.action vertex⁻¹ ((family vertex : W → S) vertex) ∣
    data.action vertex⁻¹ (data.action vertex ((value : W → S) vertex)) at hmapped
  simpa only [untwistEquiv_apply, ← data.action_mul_apply, inv_mul_cancel,
    data.action_one_apply] using hmapped

variable [WellFoundedLT W] [Fintype W] [IsDomain S]

include hsupport hdiagonal hdivides in
/-- Triangular reflection splines form a basis for the orbit scalar structure. -/
noncomputable def rightTriangularBasis :
    letI := data.rightAlgebra selected
    Module.Basis W S (data.Spline selected) := by
  letI := data.rightAlgebra selected
  exact ((data.fixedLabelGraph selected).triangularBasis
    (fun vertex => data.untwistEquiv selected (family vertex))
    (data.untwist_family_support selected family hsupport)
    (data.untwist_family_diagonal selected family hdiagonal)
    (data.untwist_family_divides selected family hdivides)).map
      (data.rightUntwistLinearEquiv selected).symm

/-- The transferred right basis has the family as its basis vectors. -/
theorem rightTriangularBasis_apply (vertex : W) :
    letI := data.rightAlgebra selected
    data.rightTriangularBasis selected family hsupport hdiagonal hdivides vertex =
      family vertex := by
  let := data.rightAlgebra selected
  simp only [rightTriangularBasis, Module.Basis.map_apply,
    IdealLabeledGraph.triangularBasis_apply]
  exact (data.untwistEquiv selected).symm_apply_apply (family vertex)

end Schubert.Splines.ReflectionGraphData
