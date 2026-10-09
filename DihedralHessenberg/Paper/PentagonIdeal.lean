import DihedralHessenberg.Paper.PentagonGraph
import DihedralHessenberg.Paper.HessenbergVectorClassification
import DihedralHessenberg.Paper.HessenbergVectorDegree
import DihedralHessenberg.Paper.FlowupRecursion
import DihedralHessenberg.Paper.HessenbergLengthPolynomialClosed
import Mathlib.Tactic

/-! # The three-root pentagon ideal -/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral

private theorem selected_index (index : Fin 5) :
    positiveRoot 5 index ∈ selected.carrier ↔ index = 0 ∨ index = 1 ∨ index = 2 := by
  simp only [selected, Set.mem_insert_iff, Set.mem_singleton_iff,
    (positiveRoot_injective 5).eq_iff]

/-- The first three positive vectors form a Hessenberg ideal. -/
def ideal : HessenbergIdeal 5 (by decide) where
  toRootSubset := selected
  lower := by
    intro alpha beta horder hbeta
    obtain ⟨first, rfl⟩ := (positiveRootEquiv 5).surjective alpha
    obtain ⟨second, rfl⟩ := (positiveRootEquiv 5).surjective beta
    rw [rootOrder_layers] at horder
    change positiveRoot 5 second ∈ selected.carrier at hbeta
    change positiveRoot 5 first ∈ selected.carrier
    rw [selected_index] at hbeta ⊢
    have hindices : first = second ∨ first.val / 2 < second.val / 2 := by
      simpa only [(positiveRootEquiv 5).injective.eq_iff,
        PositiveRoot.index_equiv] using horder
    fin_cases first <;> fin_cases second
    all_goals norm_num at hindices
    all_goals norm_num at hbeta
    all_goals norm_num
  first_mem := by
    rw [simpleRoot_zero, positiveRootEquiv_val]
    exact (selected_index 0).mpr (Or.inl rfl)
  second_mem := by
    rw [simpleRoot_one, positiveRootEquiv_val]
    exact (selected_index 1).mpr (Or.inr (Or.inl rfl))

/-- The ideal selects exactly its three displayed vectors. -/
theorem carrier : ideal.carrier = {positiveRoot 5 0, positiveRoot 5 1, positiveRoot 5 2} := rfl

/-- Its indexed coordinates are the first three entries. -/
theorem indexed_roots : ideal.indexed.roots = {0, 1, 2} := by
  ext index
  rw [ideal.mem_indexed]
  change positiveRoot 5 index ∈ selected.carrier ↔ _
  simp [selected_index]

/-- Exactly three positive vectors are selected. -/
theorem cardinality : ideal.carrier.ncard = 3 := by
  rw [ideal.ncard_indexed, indexed_roots]
  decide

end Schubert.DihedralSplines.Pentagon
