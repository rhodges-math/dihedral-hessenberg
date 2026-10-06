import Schubert.DihedralSplines.HessenbergObjectBridge
import Schubert.DihedralSplines.HessenbergSymmetry
import Schubert.Dihedral.LongestReversal

/-! # Longest-element complementation of vector Hessenberg degrees -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

/-- Longest-related selected inversion counts sum to the selected root cardinality. -/
theorem length_longest_add {n : ℕ} {hthree : 3 ≤ n} (ideal : HessenbergIdeal n hthree)
    (element : DihedralGroup n) :
    ideal.toRootSubset.length (longestElement n hthree * element) +
      ideal.toRootSubset.length element = ideal.carrier.ncard := by
  rw [ideal.length_indexed, ideal.length_indexed, ideal.ncard_indexed]
  exact ideal.indexed.length_alternatingWord_top_mul_add element

end Schubert.DihedralSplines.HessenbergIdeal
