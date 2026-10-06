import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Homogeneous projections and coordinates of a homogeneous basis

Direct-sum projections select exactly those basis coordinates with their degree.
-/

noncomputable section

namespace Schubert.Splines

variable {K M I D : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable [DecidableEq D] (pieces : D → Submodule K M) [DirectSum.Decomposition pieces]

/-- The ambient linear projection onto one internal homogeneous component. -/
def homogeneousProjection (degree : D) : M →ₗ[K] M :=
  (pieces degree).subtype.comp
    ((DirectSum.component K D (fun index => pieces index) degree).comp
      (DirectSum.decomposeLinearEquiv pieces).toLinearMap)

/-- Projection onto the degree of a homogeneous vector fixes that vector. -/
theorem homogeneousProjection_of_mem (degree : D) {value : M}
    (hvalue : value ∈ pieces degree) : homogeneousProjection pieces degree value = value :=
  DirectSum.decompose_of_mem_same pieces hvalue

/-- Projection onto a different degree of a homogeneous vector vanishes. -/
theorem homogeneousProjection_of_mem_ne (degree other : D) {value : M}
    (hvalue : value ∈ pieces other) (hne : other ≠ degree) :
    homogeneousProjection pieces degree value = 0 :=
  DirectSum.decompose_of_mem_ne pieces hvalue hne

/-- A homogeneous basis vector is fixed or killed according to its degree. -/
theorem homogeneousProjection_basis
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) (index : I) :
    homogeneousProjection pieces degree (basis index) =
      if degrees index = degree then basis index else 0 := by
  split_ifs with heq
  · exact homogeneousProjection_of_mem pieces degree (heq ▸ hbasis index)
  · exact homogeneousProjection_of_mem_ne pieces degree (degrees index) (hbasis index) heq

/-- Projection keeps exactly the coordinates of the selected degree. -/
theorem homogeneousProjection_repr [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index))
    (degree : D) (value : M) (index : I) :
    basis.repr (homogeneousProjection pieces degree value) index =
      if degrees index = degree then basis.repr value index else 0 := by
  classical
  change basis.coord index (homogeneousProjection pieces degree value) =
    if degrees index = degree then basis.coord index value else 0
  conv_lhs => rw [← basis.sum_repr value, map_sum]
  rw [map_sum]
  simp only [map_smul, homogeneousProjection_basis pieces basis degrees hbasis]
  simp only [apply_ite, map_zero, Module.Basis.coord_apply, basis.repr_self_apply]
  rw [Finset.sum_eq_single index]
  · by_cases heq : degrees index = degree <;> simp [heq]
  · intro other _ hne
    simp [hne]
  · intro hnot
    exact (hnot (Finset.mem_univ index)).elim
/-- A homogeneous vector has zero basis coefficients at every other degree. -/
theorem homogeneousBasis_repr_eq_zero_of_mem [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index))
    (degree : D) {value : M} (hvalue : value ∈ pieces degree)
    (index : I) (hne : degrees index ≠ degree) : basis.repr value index = 0 := by
  have hprojection := homogeneousProjection_repr pieces basis degrees hbasis degree value index
  rw [homogeneousProjection_of_mem pieces degree hvalue, ite_eq_right hne] at hprojection
  exact hprojection

/-- A homogeneous component is spanned exactly by the basis vectors of its degree. -/
theorem homogeneousPiece_eq_span_basis_degree [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    pieces degree = Submodule.span K
      (Set.range fun index : {index // degrees index = degree} => basis index) := by
  classical
  apply le_antisymm
  · intro value hvalue
    rw [← basis.sum_repr value]
    apply Submodule.sum_mem
    intro index _
    by_cases heq : degrees index = degree
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨index, heq⟩, rfl⟩)
    · rw [homogeneousBasis_repr_eq_zero_of_mem pieces basis degrees hbasis degree hvalue index heq,
        zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    change basis index.val ∈ pieces degree
    have hmember := hbasis index.val
    rw [index.property] at hmember
    exact hmember

/-- Restrict a homogeneous basis to one homogeneous component. -/
def homogeneousPieceBasis [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    Module.Basis {index // degrees index = degree} K (pieces degree) :=
  (Module.Basis.span (basis.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (homogeneousPiece_eq_span_basis_degree
      pieces basis degrees hbasis degree).symm)

/-- Component rank counts the homogeneous basis vectors of that degree. -/
theorem homogeneousPieceBasis_finrank [Fintype I] [StrongRankCondition K]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    Module.finrank K (pieces degree) = Nat.card {index // degrees index = degree} :=
  Module.finrank_eq_nat_card_basis (homogeneousPieceBasis pieces basis degrees hbasis degree)
/-- Restricted homogeneous basis vectors are the ambient basis vectors. -/
theorem homogeneousPieceBasis_apply [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D)
    (index : {index // degrees index = degree}) :
    (homogeneousPieceBasis pieces basis degrees hbasis degree index : M) = basis index := by
  simp only [homogeneousPieceBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]
  rfl

/-- Every component of a module with a finite homogeneous basis is finite. -/
theorem homogeneousPieceBasis_finite [Fintype I]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    Module.Finite K (pieces degree) :=
  Module.Finite.of_basis (homogeneousPieceBasis pieces basis degrees hbasis degree)
end Schubert.Splines
