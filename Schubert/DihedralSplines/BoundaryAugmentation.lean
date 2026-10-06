import Schubert.DihedralSplines.BlockIndependence

/-! # Boundary products under addition of one root -/

noncomputable section

namespace Schubert.Dihedral.RootSubset

open Schubert.DihedralSplines

variable {n : ℕ} [NeZero n] (selected larger : RootSubset n)

omit [NeZero n] in
/-- Adding an absent outgoing root inserts precisely one factor into the boundary-root set. -/
theorem boundaryRoots_insert (delta : PositiveRoot n)
    (hcarrier : larger.carrier = insert delta.val selected.carrier)
    (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n)
    (hleaves : vertex * delta.reflection ∉ vertices) :
    larger.boundaryRoots vertices vertex = insert delta (selected.boundaryRoots vertices vertex) :=
  by
  classical
  ext alpha
  simp only [mem_boundaryRoots, Finset.mem_insert]
  change (alpha.val ∈ larger.carrier ∧ _) ↔ _
  rw [hcarrier, Set.mem_insert_iff]
  constructor
  · rintro ⟨hequal | hselected, houtside⟩
    · exact Or.inl (Subtype.ext hequal)
    · exact Or.inr ⟨hselected, houtside⟩
  · rintro (hequal | ⟨hselected, houtside⟩)
    · subst alpha
      exact ⟨Or.inl rfl, hleaves⟩
    · exact ⟨Or.inr hselected, houtside⟩

/-- An added outgoing root multiplies the boundary product by its exact transformed form. -/
theorem boundaryProduct_insert (delta : PositiveRoot n)
    (hmissing : delta.val ∉ selected.carrier)
    (hcarrier : larger.carrier = insert delta.val selected.carrier)
    (vertices : Set (DihedralGroup n)) (vertex : DihedralGroup n)
    (hleaves : vertex * delta.reflection ∉ vertices) :
    larger.boundaryProduct vertices vertex =
      polynomialAction n vertex delta.form * selected.boundaryProduct vertices vertex := by
  classical
  have hnot : delta ∉ selected.boundaryRoots vertices vertex := by
    exact fun hmem => hmissing ((selected.mem_boundaryRoots vertices vertex delta).mp hmem).1
  unfold boundaryProduct
  rw [selected.boundaryRoots_insert larger delta hcarrier vertices vertex hleaves,
    Finset.prod_insert hnot, ← PositiveRoot.action_form]

/-- On any support left by the added root, the boundary function gains the same pointwise factor. -/
theorem boundaryFunction_insert (delta : PositiveRoot n)
    (hmissing : delta.val ∉ selected.carrier)
    (hcarrier : larger.carrier = insert delta.val selected.carrier)
    (vertices : Set (DihedralGroup n)) (coefficient : DihedralGroup n → ℂ)
    (hleaves : ∀ vertex ∈ vertices, vertex * delta.reflection ∉ vertices)
    (vertex : DihedralGroup n) :
    larger.boundaryFunction vertices coefficient vertex =
      polynomialAction n vertex delta.form * selected.boundaryFunction vertices coefficient vertex
      :=
  by
  classical
  by_cases hvertex : vertex ∈ vertices
  · rw [boundaryFunction, boundaryFunction, ite_eq_left hvertex, ite_eq_left hvertex,
      selected.boundaryProduct_insert larger delta hmissing hcarrier vertices vertex
        (hleaves vertex hvertex)]
    ring
  · simp only [boundaryFunction, ite_eq_right hvertex, mul_zero]

/-- Independence after a common pointwise boundary factor implies independence before it. -/
theorem independent_of_insert {I : Type*} (delta : PositiveRoot n)
    (hmissing : delta.val ∉ selected.carrier)
    (hcarrier : larger.carrier = insert delta.val selected.carrier)
    (vertices : I → Set (DihedralGroup n)) (coefficient : I → DihedralGroup n → ℂ)
    (hleaves : ∀ index vertex, vertex ∈ vertices index →
      vertex * delta.reflection ∉ vertices index)
    (hindependent : LinearIndependent ℂ (fun index =>
      larger.boundaryFunction (vertices index) (coefficient index))) :
    LinearIndependent ℂ (fun index =>
      selected.boundaryFunction (vertices index) (coefficient index)) := by
  let transform : (DihedralGroup n → CoordinatePolynomial) →ₗ[ℂ]
      (DihedralGroup n → CoordinatePolynomial) :=
    { toFun := fun value vertex => polynomialAction n vertex delta.form * value vertex
      map_add' := fun first second => by funext vertex; exact mul_add _ _ _
      map_smul' := fun scalar value => by
        funext vertex
        simp only [Pi.smul_apply, mul_smul_comm, RingHom.id_apply] }
  apply LinearIndependent.of_comp transform
  have heq : transform ∘ (fun index =>
      selected.boundaryFunction (vertices index) (coefficient index)) =
      (fun index => larger.boundaryFunction (vertices index) (coefficient index)) := by
    funext index vertex
    exact (selected.boundaryFunction_insert larger delta hmissing hcarrier
      (vertices index) (coefficient index) (hleaves index) vertex).symm
  rw [heq]
  exact hindependent
end Schubert.Dihedral.RootSubset
