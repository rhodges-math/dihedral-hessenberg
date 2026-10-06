import Schubert.Dihedral.RootSubset
import Schubert.Dihedral.RootObjectAction
import Schubert.DihedralSplines.Spline
import Schubert.Splines.PolynomialGraph

/-! # Endpoint pairs and their geometric polynomial labels -/

noncomputable section

namespace Schubert.Dihedral

open Schubert.Dihedral Schubert.Splines

namespace RootSubset

variable {n : ℕ} (selected : Schubert.Dihedral.RootSubset n)

/-- Ordered endpoint pairs joined by a selected root reflection. -/
def edges : Set (DihedralGroup n × DihedralGroup n) :=
  {pair | ∃ alpha : PositiveRoot n,
    alpha.val ∈ selected ∧ pair.2 = pair.1 * alpha.reflection}

/-- An edge is an ordered pair belonging to the geometric edge set. -/
abbrev Edges := ↥selected.edges

/-- Edge membership is exactly a selected reflection endpoint equality. -/
theorem mem_edges (pair : DihedralGroup n × DihedralGroup n) :
    pair ∈ selected.edges ↔ ∃ alpha : PositiveRoot n,
      alpha.val ∈ selected ∧ pair.2 = pair.1 * alpha.reflection := Iff.rfl

/-- The selected positive root belonging to an endpoint pair. -/
def edgeRoot (edge : selected.Edges) : PositiveRoot n :=
  Classical.choose edge.property

/-- The recovered root is selected. -/
theorem edgeRoot_mem (edge : selected.Edges) : (selected.edgeRoot edge).val ∈ selected :=
  (Classical.choose_spec edge.property).1

/-- The recovered root reflection joins the specified endpoints. -/
theorem edgeRoot_endpoint (edge : selected.Edges) :
    edge.val.2 = edge.val.1 * (selected.edgeRoot edge).reflection :=
  (Classical.choose_spec edge.property).2

/-- Endpoint pairs determine their selected positive root uniquely. -/
theorem edgeRoot_unique (edge : selected.Edges) (alpha : PositiveRoot n)
    (hendpoint : edge.val.2 = edge.val.1 * alpha.reflection) :
    selected.edgeRoot edge = alpha := by
  apply PositiveRoot.reflection_injective n
  exact mul_left_cancel ((selected.edgeRoot_endpoint edge).symm.trans hendpoint)

/-- The endpoint pair determined by a selected root reflection. -/
def edge (vertex : DihedralGroup n) (alpha : PositiveRoot n) (hmem : alpha.val ∈ selected) :
    selected.Edges :=
  ⟨(vertex, vertex * alpha.reflection), alpha, hmem, rfl⟩

/-- A reflected endpoint pair recovers its positive root. -/
@[simp] theorem edgeRoot_edge (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hmem : alpha.val ∈ selected) : selected.edgeRoot (selected.edge vertex alpha hmem) = alpha :=
  selected.edgeRoot_unique _ alpha rfl

/-- The polynomial label is the linear form of the transformed root vector. -/
def edgeLabel (pair : selected.Edges) : CoordinatePolynomial :=
  linearPolynomial (complexify (realAction n pair.val.1 (selected.edgeRoot pair).val))

/-- The label at a selected reflection edge has its exact geometric generator. -/
theorem edgeLabel_edge (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hmem : alpha.val ∈ selected) :
    selected.edgeLabel (selected.edge vertex alpha hmem) =
      linearPolynomial (complexify (realAction n vertex alpha.val)) := by
  rw [edgeLabel, edgeRoot_edge]
  rfl

/-- The endpoint graph retains its polynomial labels. -/
def graph : PolynomialGraph CoordinatePolynomial (DihedralGroup n) selected.Edges where
  source pair := pair.val.1
  target pair := pair.val.2
  label := selected.edgeLabel

/-- Indexing edges preserves the ordered endpoint pairs. -/
def edgeEquiv :
    (DihedralGroup n × selected.indices) ≃ selected.Edges :=
  Equiv.ofBijective
    (fun pair => selected.edge pair.1 (positiveRootEquiv n pair.2)
      (by simpa only [positiveRootEquiv_val, mem_indices] using pair.2.property)) (by
      constructor
      · intro first second heq
        have hfirst := congrArg (fun pair => pair.val.1) heq
        have hsecond := congrArg (fun pair => pair.val.2) heq
        change first.1 = second.1 at hfirst
        apply Prod.ext hfirst
        apply Subtype.ext
        apply rootReflection_injective n
        change first.1 * (positiveRootEquiv n first.2).reflection =
          second.1 * (positiveRootEquiv n second.2).reflection at hsecond
        simp only [PositiveRoot.reflection_equiv] at hsecond
        exact mul_left_cancel (by simpa only [hfirst] using hsecond)
      · intro pair
        let alpha := selected.edgeRoot pair
        have hmem : alpha.index ∈ selected.indices := by
          change positiveRoot n alpha.index ∈ selected
          rw [PositiveRoot.index_val]
          exact selected.edgeRoot_mem pair
        refine ⟨(pair.val.1, ⟨alpha.index, hmem⟩), ?_⟩
        apply Subtype.ext
        change (pair.val.1, pair.val.1 * (positiveRootEquiv n alpha.index).reflection) = pair.val
        rw [PositiveRoot.reflection_equiv]
        refine Prod.ext rfl ?_
        exact (selected.edgeRoot_endpoint pair).symm)

/-- The indexed edge equivalence preserves both endpoints. -/
theorem edgeEquiv_apply (vertex : DihedralGroup n) (index : selected.indices) :
    (selected.edgeEquiv (vertex, index)).val = (vertex, vertex * rootReflection index) := by
  change (vertex, vertex * (positiveRootEquiv n index).reflection) = _
  rw [PositiveRoot.reflection_equiv]

/-- The indexed and geometric graphs have exactly the same polynomial generator. -/
theorem edgeEquiv_label [NeZero n] (vertex : DihedralGroup n) (index : selected.indices) :
    selected.edgeLabel (selected.edgeEquiv (vertex, index)) =
      polynomialAction n vertex (rootPolynomial n index) := by
  have hmem : (positiveRootEquiv n index).val ∈ selected := by
    simpa only [positiveRootEquiv_val, mem_indices] using index.property
  change selected.edgeLabel (selected.edge vertex (positiveRootEquiv n index) hmem) = _
  rw [edgeLabel_edge, positiveRootEquiv_val,
    realAction_complexify n vertex _ (Or.inl ⟨index, rfl⟩)]
  exact (polynomialAction_linearPolynomial n vertex (complexPositiveRoot n index)).symm


/-- Geometric edge membership agrees with the finite indexed reflection predicate. -/
theorem mem_edges_iff_index (pair : DihedralGroup n × DihedralGroup n) :
    pair ∈ selected.edges ↔ ∃ index ∈ selected.indices,
      pair.2 = pair.1 * rootReflection index := by
  constructor
  · rintro ⟨alpha, hmem, hendpoint⟩
    have hindex : alpha.index ∈ selected.indices := by
      change positiveRoot n alpha.index ∈ selected
      rw [PositiveRoot.index_val]
      exact hmem
    exact ⟨alpha.index, hindex, hendpoint⟩
  · rintro ⟨index, hindex, hendpoint⟩
    refine ⟨positiveRootEquiv n index, hindex, ?_⟩
    simpa only [PositiveRoot.reflection_equiv] using hendpoint

/-- The geometric generator equals polynomial action on the recovered root form. -/
theorem edgeLabel_eq_action [NeZero n] (pair : selected.Edges) :
    selected.edgeLabel pair = polynomialAction n pair.val.1 (selected.edgeRoot pair).form :=
  (PositiveRoot.action_form _ _).symm

/-- Reversing a geometric edge exchanges its endpoints. -/
def reverse (pair : selected.Edges) : selected.Edges :=
  ⟨(pair.val.2, pair.val.1), selected.edgeRoot pair, selected.edgeRoot_mem pair, by
    rw [selected.edgeRoot_endpoint pair, mul_assoc, PositiveRoot.reflection_square, mul_one]⟩

/-- Reversal swaps the ordered endpoint pair. -/
theorem reverse_val (pair : selected.Edges) :
    (selected.reverse pair).val = (pair.val.2, pair.val.1) := rfl

/-- Reversal recovers the same positive root, not the transformed signed root. -/
theorem edgeRoot_reverse (pair : selected.Edges) :
    selected.edgeRoot (selected.reverse pair) = selected.edgeRoot pair := by
  apply selected.edgeRoot_unique
  change pair.val.1 = pair.val.2 * (selected.edgeRoot pair).reflection
  rw [selected.edgeRoot_endpoint pair, mul_assoc, PositiveRoot.reflection_square, mul_one]

/-- Reversing an ordered edge negates its specified polynomial generator. -/
theorem label_reverse [NeZero n] (hthree : 3 ≤ n) (pair : selected.Edges) :
    selected.edgeLabel (selected.reverse pair) = -selected.edgeLabel pair := by
  rw [edgeLabel_eq_action, edgeLabel_eq_action, edgeRoot_reverse]
  change polynomialAction n pair.val.2 (selected.edgeRoot pair).form = _
  rw [selected.edgeRoot_endpoint pair]
  simp only [PositiveRoot.form_index, PositiveRoot.reflection]
  exact (Schubert.DihedralSplines.dihedralReflectionData n hthree).reflection_label_reverse
    pair.val.1 (selected.edgeRoot pair).index

end RootSubset

end Schubert.Dihedral
