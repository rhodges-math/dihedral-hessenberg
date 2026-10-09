import DihedralHessenberg.Splines.HomogeneousBasis

/-! # Degree restriction of an arbitrary homogeneous basis

Each vector has finitely supported coordinates even when the whole basis is infinite.
Finite-dimensionality of one degree requires only finiteness of its own degree fiber.
-/

noncomputable section

namespace Schubert.Splines

variable {K M I D : Type*} [CommRing K] [AddCommGroup M] [Module K M]
variable [DecidableEq D] (pieces : D → Submodule K M) [DirectSum.Decomposition pieces]

/-- Homogeneous projection selects coordinates of its degree, for an arbitrary basis. -/
theorem arbitraryHomogeneousProjection_repr
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index))
    (degree : D) (value : M) (index : I) :
    basis.repr (homogeneousProjection pieces degree value) index =
      if degrees index = degree then basis.repr value index else 0 := by
  classical
  change basis.coord index (homogeneousProjection pieces degree value) =
    if degrees index = degree then basis.coord index value else 0
  conv_lhs =>
    rw [← basis.linearCombination_repr value, Finsupp.linearCombination_apply, Finsupp.sum,
      map_sum]
  rw [map_sum]
  simp only [map_smul, homogeneousProjection_basis pieces basis degrees hbasis]
  simp only [apply_ite, map_zero, Module.Basis.coord_apply, basis.repr_self_apply]
  rw [Finset.sum_eq_single index]
  · by_cases heq : degrees index = degree <;> simp [heq]
  · intro other _ hne
    simp [hne]
  · intro hnot
    simp [Finsupp.notMem_support_iff.mp hnot]

/-- A vector in one homogeneous degree has no coordinates at the other degrees. -/
theorem _root_.Schubert.Splines.HomogeneousBasis.repr_zero_of_degree_ne
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index))
    (degree : D) {value : M} (hvalue : value ∈ pieces degree)
    (index : I) (hne : degrees index ≠ degree) : basis.repr value index = 0 := by
  have hprojection := arbitraryHomogeneousProjection_repr
    pieces basis degrees hbasis degree value index
  rw [homogeneousProjection_of_mem pieces degree hvalue, ite_eq_right hne] at hprojection
  exact hprojection

/-- A degree piece is exactly the span of its degree fiber of an arbitrary homogeneous basis. -/
theorem _root_.Schubert.Splines.HomogeneousBasis.piece_eq_span_degree
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    pieces degree = Submodule.span K
      (Set.range fun index : {index // degrees index = degree} => basis index) := by
  classical
  apply le_antisymm
  · intro value hvalue
    rw [← basis.linearCombination_repr value, Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro index _
    by_cases heq : degrees index = degree
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨index, heq⟩, rfl⟩)
    · rw [_root_.Schubert.Splines.HomogeneousBasis.repr_zero_of_degree_ne
        pieces basis degrees hbasis degree hvalue index heq, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro value ⟨index, rfl⟩
    change basis index.val ∈ pieces degree
    have hmember := hbasis index.val
    rw [index.property] at hmember
    exact hmember

/-- Restrict an arbitrary homogeneous basis to one degree piece. -/
def arbitraryHomogeneousPieceBasis
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    Module.Basis {index // degrees index = degree} K (pieces degree) :=
  (Module.Basis.span (basis.linearIndependent.comp Subtype.val Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (_root_.Schubert.Splines.HomogeneousBasis.piece_eq_span_degree
      pieces basis degrees hbasis degree).symm)

/-- Degree rank counts its fiber even for an infinite ambient homogeneous basis. -/
theorem arbitraryHomogeneousPieceBasis_finrank [StrongRankCondition K]
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D) :
    Module.finrank K (pieces degree) = Nat.card {index // degrees index = degree} :=
  Module.finrank_eq_nat_card_basis
    (arbitraryHomogeneousPieceBasis pieces basis degrees hbasis degree)

/-- A finite degree fiber suffices for a finite homogeneous component. -/
theorem arbitraryHomogeneousPieceBasis_finite
    (basis : Module.Basis I K M) (degrees : I → D)
    (hbasis : ∀ index, basis index ∈ pieces (degrees index)) (degree : D)
    [Finite {index // degrees index = degree}] : Module.Finite K (pieces degree) :=
  Module.Finite.of_basis (arbitraryHomogeneousPieceBasis pieces basis degrees hbasis degree)

end Schubert.Splines
