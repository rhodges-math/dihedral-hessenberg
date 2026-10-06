import Schubert.DihedralSplines.HessenbergVectorDegree
import Schubert.DihedralSplines.HessenbergReflectionLength
import Schubert.DihedralSplines.HessenbergLengthRanges

/-! # Simple edges and length ranges for even root cardinality -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

private theorem simple_index {alpha : PositiveRoot n}
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ∃ simple : Fin 2, alpha = simpleRoot n hthree simple := by
  rcases hsimple with hfirst | hsecond
  · exact ⟨0, hfirst⟩
  · exact ⟨1, hsecond⟩

/-- For even cardinality, simple ascents are edges exactly in the two outer length ranges. -/
theorem edge_ascent_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1) :
    (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ↔
      length n hthree element < half ∨ n - half ≤ length n hthree element := by
  obtain ⟨simple, rfl⟩ := simple_index hsimple
  rw [simpleRoot_reflection] at hascent ⊢
  rw [RootSubset.mem_edges_iff_index, ← ideal.indexed_roots]
  simp only [Finset.mem_coe]
  exact ideal.indexed.simple_ascent_edge_iff_of_even half
    (by simpa only [ideal.ncard_indexed] using hcard) simple element hascent

/-- For even cardinality, simple descents are edges exactly in the two outer length ranges. -/
theorem edge_descent_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hdescent : length n hthree (alpha.reflection * element) + 1 = length n hthree element) :
    (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ↔
      length n hthree element ≤ half ∨ n - half < length n hthree element := by
  obtain ⟨simple, rfl⟩ := simple_index hsimple
  rw [simpleRoot_reflection] at hdescent ⊢
  rw [RootSubset.mem_edges_iff_index, ← ideal.indexed_roots]
  simp only [Finset.mem_coe]
  exact ideal.indexed.simple_descent_edge_iff_of_even half
    (by simpa only [ideal.ncard_indexed] using hcard) simple element hdescent

/-- Even-cardinality inversion degrees are constant between the two outer ranges. -/
theorem length_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (element : DihedralGroup n) :
    ideal.toRootSubset.length element =
      if length n hthree element ≤ half then length n hthree element
      else if length n hthree element < n - half then half
      else ideal.carrier.ncard - (n - length n hthree element) := by
  rw [ideal.length_indexed, ideal.ncard_indexed]
  exact ideal.indexed.length_piecewise_of_even half
    (by simpa only [ideal.ncard_indexed] using hcard) element

end Schubert.DihedralSplines.HessenbergIdeal
