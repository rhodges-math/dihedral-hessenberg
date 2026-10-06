import Schubert.Dihedral.CyclicPeriod
import Schubert.Dihedral.RootBlock
import Mathlib.Algebra.Group.Fin.Basic

/-! # Cyclic intervals as alternating blocks -/

noncomputable section

namespace Schubert.Dihedral.Cyclic

/-- A cyclic interval is the vertex set of consecutive polygon positions. -/
def interval (n : ℕ) (hthree : 3 ≤ n) (start : Fin (2 * n)) (size : ℕ) :
    Finset (DihedralGroup n) := by
  classical
  exact (Finset.range size).image fun position =>
    vertex n hthree ⟨(start.val + position) % (2 * n), Nat.mod_lt _ (by omega)⟩

variable {n : ℕ} {hthree : 3 ≤ n}

/-- The forward root order is prescribed by the parity of the starting vertex. -/
theorem forward_prefix (start : Fin (2 * n)) (size : ℕ) :
    vertex n hthree start *
      (if Even start.val then
        (simpleRoot n hthree 0).alternatingProduct (simpleRoot n hthree 1) size
      else (simpleRoot n hthree 1).alternatingProduct (simpleRoot n hthree 0) size) =
      vertex n hthree ⟨(start.val + size) % (2 * n), Nat.mod_lt _ (by omega)⟩ := by
  rw [vertex_mod]
  exact (PositiveRoot.alternating_append _ _ start.val size).symm

/-- An even-start cyclic interval is the first-root alternating block. -/
theorem interval_even (start : Fin (2 * n)) (half : ℕ) (heven : Even start.val) :
    interval n hthree start (2 * half + 2) =
      alternatingBlock (vertex n hthree start) (simpleRoot n hthree 0)
        (simpleRoot n hthree 1) half := by
  classical
  apply Finset.image_congr
  intro position _
  simpa only [ite_eq_left heven] using
    (forward_prefix (n := n) (hthree := hthree) start position).symm

/-- An odd-start cyclic interval is the second-root alternating block. -/
theorem interval_odd (start : Fin (2 * n)) (half : ℕ) (hodd : ¬Even start.val) :
    interval n hthree start (2 * half + 2) =
      alternatingBlock (vertex n hthree start) (simpleRoot n hthree 1)
        (simpleRoot n hthree 0) half := by
  classical
  apply Finset.image_congr
  intro position _
  simpa only [ite_eq_right hodd] using
    (forward_prefix (n := n) (hthree := hthree) start position).symm


/-- Membership is measured by the standard cyclic difference of positions. -/
theorem mem_interval (start target : Fin (2 * n)) (size : ℕ) (hsize : size ≤ 2 * n) :
    vertex n hthree target ∈ interval n hthree start size ↔ (target - start).val < size := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  rw [interval, Finset.mem_image]
  constructor
  · rintro ⟨position, hposition, heq⟩
    have hlt := Finset.mem_range.mp hposition
    have hbound : position < 2 * n := by omega
    have hindices := injective heq
    change start + ⟨position, hbound⟩ = target at hindices
    have hsub : (⟨position, hbound⟩ : Fin (2 * n)) = target - start := by
      apply eq_sub_iff_add_eq.mpr
      rwa [add_comm]
    have hval := congrArg Fin.val hsub
    change position = (target - start).val at hval
    omega
  · intro hlt
    refine ⟨(target - start).val, Finset.mem_range.mpr hlt, ?_⟩
    apply congrArg (vertex n hthree)
    change start + (target - start) = target
    exact add_sub_cancel _ _

/-- An interval shorter than a complete circuit has its prescribed cardinality. -/
theorem interval_card (start : Fin (2 * n)) (size : ℕ) (hsize : size ≤ 2 * n) :
    (interval n hthree start size).card = size := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  rw [interval, Finset.card_image_of_injOn, Finset.card_range]
  intro first hfirst second hsecond heq
  have hfirstBound : first < 2 * n := by have := Finset.mem_range.mp hfirst; omega
  have hsecondBound : second < 2 * n := by have := Finset.mem_range.mp hsecond; omega
  have hindices := injective heq
  change start + ⟨first, hfirstBound⟩ = start + ⟨second, hsecondBound⟩ at hindices
  exact congrArg Fin.val (add_left_cancel hindices)

/-- A nonempty interval of at most half a circuit determines its initial position. -/
theorem interval_injective (size : ℕ) (hpositive : 0 < size) (hsize : size ≤ n) :
    Function.Injective (fun start : Fin (2 * n) => interval n hthree start size) := by
  classical
  let : NeZero (2 * n) := ⟨by omega⟩
  intro first second heq
  change interval n hthree first size = interval n hthree second size at heq
  have hfirst : vertex n hthree first ∈ interval n hthree first size := by
    rw [mem_interval _ _ _ (by omega), sub_self, Fin.val_zero]
    exact hpositive
  have hsecond : vertex n hthree second ∈ interval n hthree second size := by
    rw [mem_interval _ _ _ (by omega), sub_self, Fin.val_zero]
    exact hpositive
  rw [heq, mem_interval _ _ _ (by omega)] at hfirst
  rw [← heq, mem_interval _ _ _ (by omega)] at hsecond
  fin_omega

end Schubert.Dihedral.Cyclic
