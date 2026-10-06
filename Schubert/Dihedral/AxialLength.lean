import Schubert.Dihedral.AxialDegreeCard
import Schubert.Dihedral.LengthCount
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Card

/-! # Canonical length matching of axial basis weights -/

namespace Schubert.Dihedral

/-- Canonical length fibers have the endpoint and intermediate dihedral cardinalities. -/
theorem length_fiber_card (n : ℕ) (hthree : 3 ≤ n) (degree : ℕ) :
    Nat.card {element : DihedralGroup n // length n hthree element = degree} =
      if degree = 0 ∨ degree = n then 1 else if degree < n then 2 else 0 := by
  classical
  let : NeZero n := ⟨by omega⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  by_cases hzero : degree = 0
  · subst degree
    rw [card_length_eq_zero]
    simp
  by_cases htop : degree = n
  · subst degree
    rw [card_length_eq_n]
    simp
  by_cases hmiddle : degree < n
  · rw [card_length_eq_of_positive_lt degree (by omega) hmiddle]
    simp [hzero, htop, hmiddle]
  · have hempty : (Finset.univ.filter fun element : DihedralGroup n =>
        length n hthree element = degree) = ∅ := by
      ext element
      have hbound := length_le_polygon_parameter n hthree element
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    rw [hempty, Finset.card_empty]
    simp [hzero, htop, hmiddle]

/-- Axial basis indices can be matched with vertices preserving their canonical lengths. -/
theorem exists_axial_length_equiv (n : ℕ) (hthree : 3 ≤ n) :
    ∃ equiv : (Fin n × Fin 2) ≃ DihedralGroup n, ∀ index,
      length n hthree (equiv index) =
        if index.1.val = 0 then if index.2 = 0 then 0 else n
        else if index.2 = 0 then n - index.1.val else index.1.val := by
  classical
  let : NeZero n := ⟨by omega⟩
  let weight (index : Fin n × Fin 2) :=
    if index.1.val = 0 then if index.2 = 0 then 0 else n
    else if index.2 = 0 then n - index.1.val else index.1.val
  have hcard (degree : ℕ) :
      Fintype.card {index : Fin n × Fin 2 // weight index = degree} =
        Fintype.card {element : DihedralGroup n // length n hthree element = degree} := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card {index : Fin n × Fin 2 //
      (if index.1.val = 0 then if index.2 = 0 then 0 else n
        else if index.2 = 0 then n - index.1.val else index.1.val) = degree} = _
    rw [axial_rotation_block_degree_fiber_card n degree (by omega),
      length_fiber_card n hthree degree]
  let fibers (degree : ℕ) := Fintype.equivOfCardEq (hcard degree)
  exact ⟨Equiv.ofFiberEquiv fibers, Equiv.ofFiberEquiv_map fibers⟩

end Schubert.Dihedral
