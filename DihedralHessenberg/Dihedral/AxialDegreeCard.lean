import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-! # Counting degrees of the axial rotation blocks

The two columns of axial blocks have degrees 0 through n-1 and 1 through n.
Every intermediate degree occurs twice, and the two endpoints occur once.
-/

namespace Schubert.Dihedral

/-- The axial block degree fibers have the dihedral coinvariant degree cardinalities. -/
theorem axial_rotation_block_degree_fiber_card (n degree : ℕ) (hpositive : 0 < n) :
    Nat.card {index : Fin n × Fin 2 //
      (if index.1.val = 0 then if index.2 = 0 then 0 else n
        else if index.2 = 0 then n - index.1.val else index.1.val) = degree} =
      if degree = 0 ∨ degree = n then 1 else if degree < n then 2 else 0 := by
  classical
  let degrees (index : Fin n × Fin 2) :=
    if index.1.val = 0 then if index.2 = 0 then 0 else n
      else if index.2 = 0 then n - index.1.val else index.1.val
  change Nat.card ({index : Fin n × Fin 2 | degrees index = degree} : Set _) = _
  rw [Nat.card_coe_set_eq]
  by_cases hzero : degree = 0
  · subst degree
    have hset : {index : Fin n × Fin 2 | degrees index = 0} =
        {(⟨0, hpositive⟩, 0)} := by
      ext ⟨⟨row, hbound⟩, coordinate⟩
      fin_cases coordinate <;> by_cases hrow : row = 0 <;>
        simp [degrees, hrow, Prod.mk.injEq, Fin.mk.injEq] <;> omega
    rw [hset, Set.ncard_singleton]
    simp
  by_cases htop : degree = n
  · subst degree
    have hset : {index : Fin n × Fin 2 | degrees index = n} =
        {(⟨0, hpositive⟩, 1)} := by
      ext ⟨⟨row, hbound⟩, coordinate⟩
      fin_cases coordinate <;> by_cases hrow : row = 0 <;>
        simp [degrees, hrow, Prod.mk.injEq, Fin.mk.injEq] <;> omega
    rw [hset, Set.ncard_singleton]
    simp
  by_cases hmiddle : degree < n
  · let first : Fin n × Fin 2 := (⟨n - degree, by omega⟩, 0)
    let second : Fin n × Fin 2 := (⟨degree, hmiddle⟩, 1)
    have hne : first ≠ second := by
      intro hequal
      have hcoordinate := congrArg Prod.snd hequal
      simp [first, second] at hcoordinate
    have hset : {index : Fin n × Fin 2 | degrees index = degree} =
        {first, second} := by
      ext ⟨⟨row, hbound⟩, coordinate⟩
      fin_cases coordinate <;> by_cases hrow : row = 0 <;>
        simp [degrees, hrow, first, second, Prod.mk.injEq, Fin.mk.injEq] <;> omega
    rw [hset, Set.ncard_pair hne]
    simp [hzero, htop, hmiddle]
  · have hset : {index : Fin n × Fin 2 | degrees index = degree} = ∅ := by
      ext ⟨⟨row, hbound⟩, coordinate⟩
      fin_cases coordinate <;> by_cases hrow : row = 0 <;>
        simp [degrees, hrow] <;> omega
    rw [hset, Set.ncard_empty]
    simp [hzero, htop, hmiddle]

end Schubert.Dihedral
