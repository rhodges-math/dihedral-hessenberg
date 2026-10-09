import DihedralHessenberg.Paper.HessenbergObjectBridge
import DihedralHessenberg.Paper.HessenbergDegreeThreshold

/-! # Low-degree inversion counts for vector Hessenberg ideals -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- Selected inversion counts agree with canonical length through the half threshold. -/
theorem length_below_half (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hhalf : 2 * half ≤ ideal.carrier.ncard) (element : DihedralGroup n)
    (hlength : length n hthree element ≤ half) :
    ideal.toRootSubset.length element = length n hthree element := by
  rw [ideal.length_indexed]
  exact ideal.indexed.length_eq_coxeter_length_of_le_half half
    (by rwa [← ideal.ncard_indexed]) element hlength

/-- Canonical lengths above the threshold have at least that many selected inversions. -/
theorem half_le_length (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hhalf : 2 * half ≤ ideal.carrier.ncard) (element : DihedralGroup n)
    (hlength : half ≤ length n hthree element) :
    half ≤ ideal.toRootSubset.length element := by
  rw [ideal.length_indexed]
  exact ideal.indexed.half_le_length_of_half_le_coxeter_length half
    (by rwa [← ideal.ncard_indexed]) element hlength

/-- Below the threshold, selected inversion fibers are canonical length fibers. -/
theorem length_fiber_below_half (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hhalf : 2 * half ≤ ideal.carrier.ncard) (degree : ℕ) (hdegree : degree < half)
    (element : DihedralGroup n) :
    ideal.toRootSubset.length element = degree ↔ length n hthree element = degree := by
  rw [ideal.length_indexed]
  exact ideal.indexed.length_eq_coxeter_below_half half
    (by rwa [← ideal.ncard_indexed]) degree hdegree element

end Schubert.DihedralSplines.HessenbergIdeal
