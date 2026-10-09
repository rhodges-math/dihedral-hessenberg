import DihedralHessenberg.Dihedral.RootAlternatingWords
import DihedralHessenberg.Paper.HessenbergObjectBridge
import DihedralHessenberg.Paper.PaperGraph
import DihedralHessenberg.Paper.HessenbergDominant

/-! # Dominance of simple vectors for a Hessenberg ideal -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A simple vector is dominant when an alternating word starting with the other
simple vector has middle H-length and exactly its prescribed simple edge. -/
noncomputable def IsDominant (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n) : Prop :=
  ∃ beta : PositiveRoot n,
    ((alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
      (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)) ∧
    ∃ size : ℕ, 0 < size ∧ size ≤ n ∧
      let element := beta.alternatingProduct alpha size
      ideal.toRootSubset.length element = ideal.carrier.ncard / 2 ∧
        (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ∧
        (element, beta.reflection * element) ∉ ideal.toRootSubset.edges

private theorem edge_indices (ideal : HessenbergIdeal n hthree) (simple : Fin 2)
    (element : DihedralGroup n) :
    (element, simpleReflection n simple * element) ∈ ideal.toRootSubset.edges ↔
      ∃ index ∈ ideal.indexed.roots,
        simpleReflection n simple * element = element * rootReflection index := by
  rw [RootSubset.mem_edges_iff_index, ← ideal.indexed_roots]
  rfl

/-- The vector dominance condition is exactly its indexed backend condition. -/
theorem isDominant_indexed (ideal : HessenbergIdeal n hthree) (simple : Fin 2) :
    ideal.IsDominant (simpleRoot n hthree simple) ↔ ideal.indexed.IsDominant simple := by
  constructor
  · rintro ⟨beta, hpair, size, hpositive, hbound, hconditions⟩
    obtain ⟨other, hfirst, hsecond⟩ :=
      simple_pair_index (simpleRoot n hthree simple) beta hpair
    have hsame := simpleRoot_injective n hthree hfirst.symm
    subst other
    subst beta
    dsimp only at hconditions
    rw [PositiveRoot.alternatingProduct_indexed, ideal.length_indexed,
      ideal.ncard_indexed] at hconditions
    refine ⟨size, hpositive, hbound, ?_⟩
    simpa only [simpleRoot_reflection, edge_indices] using hconditions
  · rintro ⟨size, hpositive, hbound, hconditions⟩
    have hpair :
        ((simpleRoot n hthree simple = simpleRoot n hthree 0 ∧
          simpleRoot n hthree simple.rev = simpleRoot n hthree 1) ∨
        (simpleRoot n hthree simple = simpleRoot n hthree 1 ∧
          simpleRoot n hthree simple.rev = simpleRoot n hthree 0)) := by
      fin_cases simple
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    refine ⟨simpleRoot n hthree simple.rev, hpair, size, hpositive, hbound, ?_⟩
    dsimp only
    rw [PositiveRoot.alternatingProduct_indexed, ideal.length_indexed, ideal.ncard_indexed]
    simpa only [simpleRoot_reflection, edge_indices] using hconditions

end Schubert.DihedralSplines.HessenbergIdeal
