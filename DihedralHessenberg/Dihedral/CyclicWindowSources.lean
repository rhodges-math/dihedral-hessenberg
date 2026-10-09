import DihedralHessenberg.Dihedral.CyclicIntervals

/-! # Interior source vertices of the cyclic evaluation window -/

namespace Schubert.Dihedral.Cyclic

/-- The identity belongs to every odd-tail interval of the prescribed block size. -/
theorem zero_in_odd_interval {n : ℕ} {hthree : 3 ≤ n} (half offset : ℕ)
    (hbound : 2 * half + 1 < n) (hoffset : offset ≤ half) :
    (1 : DihedralGroup n) ∈
      interval n hthree ⟨2 * n - (2 * offset + 1), by omega⟩ (2 * half + 2) := by
  let : NeZero (2 * n) := ⟨by omega⟩
  have hzero : vertex n hthree ⟨0, by omega⟩ = 1 := by
    rw [vertex, PositiveRoot.alternating_zero]
  rw [← hzero, mem_interval _ _ _ (by omega)]
  fin_omega

/-- The first simple vertex belongs to every nonzero even-tail interval of the block size. -/
theorem one_in_even_interval {n : ℕ} {hthree : 3 ≤ n} (half offset : ℕ)
    (hbound : 2 * half + 1 < n) (hpositive : 0 < offset) (hoffset : offset ≤ half) :
    (simpleRoot n hthree 0).reflection ∈
      interval n hthree ⟨2 * n - 2 * offset, by omega⟩ (2 * half + 2) := by
  let : NeZero (2 * n) := ⟨by omega⟩
  have hone : vertex n hthree ⟨1, by omega⟩ = (simpleRoot n hthree 0).reflection := by
    rw [vertex, PositiveRoot.alternating_succ, PositiveRoot.alternating_zero, mul_one]
  rw [← hone, mem_interval _ _ _ (by omega)]
  fin_omega

end Schubert.Dihedral.Cyclic
