import Schubert.Dihedral.CyclicVertices
import Schubert.Dihedral.AlternatingAppend
import Schubert.Dihedral.LengthParity
import Schubert.DihedralSplines.PaperGraph

/-! # Selected reflection endpoints in the cyclic evaluation window -/

namespace Schubert.Dihedral.RootSubset

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Odd tail vertices have a selected reflection edge to the identity. -/
theorem tail_odd_edge (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n, length n hthree alpha.reflection ≤ 2 * half + 1 →
      alpha.val ∈ selected) (offset : ℕ) (hoffset : offset ≤ half) :
    (1, Cyclic.vertex n hthree ⟨2 * n - (2 * offset + 1), by omega⟩) ∈ selected.edges := by
  let : NeZero n := ⟨by omega⟩
  let target := Cyclic.vertex n hthree ⟨2 * n - (2 * offset + 1), by omega⟩
  have hlength : length n hthree target = 2 * offset + 1 := by
    dsimp only [target, Cyclic.vertex]
    rw [PositiveRoot.alternating_folded_length _ _ (Or.inl ⟨rfl, rfl⟩) _ (by omega)]
    omega
  obtain ⟨alpha, halpha⟩ := (positiveReflection_iff_odd n hthree target).mpr
    (by rw [hlength]; exact ⟨offset, by omega⟩)
  refine ⟨alpha, hselected alpha (by rw [halpha, hlength]; omega), ?_⟩
  change target = 1 * alpha.reflection
  rw [one_mul, halpha]

/-- Even tail vertices have a selected reflection edge to the first simple vertex. -/
theorem tail_even_edge (selected : RootSubset n) (half : ℕ) (hbound : 2 * half + 1 < n)
    (hselected : ∀ alpha : PositiveRoot n, length n hthree alpha.reflection ≤ 2 * half + 1 →
      alpha.val ∈ selected) (offset : ℕ) (hpositive : 0 < offset) (hoffset : offset ≤ half) :
    ((simpleRoot n hthree 0).reflection,
      Cyclic.vertex n hthree ⟨2 * n - 2 * offset, by omega⟩) ∈ selected.edges := by
  let : NeZero n := ⟨by omega⟩
  let target := Cyclic.vertex n hthree ⟨2 * n - 2 * offset, by omega⟩
  let source := (simpleRoot n hthree 0).reflection
  have hword : source⁻¹ * target =
      (simpleRoot n hthree 1).alternatingProduct (simpleRoot n hthree 0)
        (2 * n - 2 * offset - 1) := by
    dsimp only [target, source, Cyclic.vertex]
    rw [PositiveRoot.reflection_inv]
    have hsize : 2 * n - 2 * offset = (2 * n - 2 * offset - 1) + 1 := by omega
    rw [hsize, PositiveRoot.alternating_succ, ← mul_assoc,
      PositiveRoot.reflection_square, one_mul, Nat.add_sub_cancel]
  have hlength : length n hthree (source⁻¹ * target) = 2 * offset + 1 := by
    rw [hword, PositiveRoot.alternating_folded_length _ _ (Or.inr ⟨rfl, rfl⟩) _ (by omega)]
    omega
  obtain ⟨alpha, halpha⟩ := (positiveReflection_iff_odd n hthree (source⁻¹ * target)).mpr
    (by rw [hlength]; exact ⟨offset, by omega⟩)
  refine ⟨alpha, hselected alpha (by rw [halpha, hlength]; omega), ?_⟩
  change target = source * alpha.reflection
  rw [halpha]
  group

end Schubert.Dihedral.RootSubset
