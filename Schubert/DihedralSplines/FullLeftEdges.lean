import Schubert.DihedralSplines.DividedDifferenceLabels
import Schubert.DihedralSplines.Spline

/-! # Left reflection conditions on the full dihedral spline graph -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral Schubert.Splines

/-- Every indexed left reflection edge is a right indexed edge at the same vertex. -/
theorem exists_right_root_of_left_endpoint (n : ℕ) [NeZero n]
    (vertex : DihedralGroup n) (index : PositiveRootIndex n) :
    ∃ rightIndex : PositiveRootIndex n,
      vertex * rootReflection rightIndex = rootReflection index * vertex := by
  obtain ⟨rightIndex, himage⟩ := exists_signed_root_image n vertex⁻¹ index
  refine ⟨rightIndex, ?_⟩
  rw [rootReflection_of_signed_image n vertex⁻¹ index rightIndex himage]
  group

/-- Full-graph splines are exactly functions satisfying the fixed-label left edge conditions. -/
theorem fullReflectionGraph_isSpline_iff_left (n : ℕ) (hthree : 3 ≤ n)
    (value : DihedralGroup n → CoordinatePolynomial) :
    ((dihedralReflectionData n hthree).reflectionGraph Set.univ).IsSpline value ↔
      ∀ vertex index, rootPolynomial n index ∣
        value vertex - value (rootReflection index * vertex) := by
  let : NeZero n := ⟨(lt_of_lt_of_le (by decide : 0 < 3) hthree).ne'⟩
  constructor
  · intro hvalue vertex index
    obtain ⟨rightIndex, hendpoint⟩ := exists_right_root_of_left_endpoint n vertex index
    have hcondition := Ideal.mem_span_singleton.mp
      (hvalue (vertex, ⟨rightIndex, Set.mem_univ _⟩))
    change polynomialAction n vertex (rootPolynomial n rightIndex) ∣
      value vertex - value (vertex * rootReflection rightIndex) at hcondition
    have hassociated := _root_.Schubert.DihedralSplines.IndexedDD.associated_of_endpoint
      n vertex rightIndex index hendpoint
    rw [hendpoint] at hcondition
    exact hassociated.dvd_iff_dvd_left.mp hcondition
  · intro hvalue ⟨vertex, rightIndex, _⟩
    obtain ⟨index, himage⟩ := exists_signed_root_image n vertex rightIndex
    have hendpoint := rootReflection_endpoint_of_signed_image n vertex rightIndex index himage
    apply Ideal.mem_span_singleton.mpr
    change polynomialAction n vertex (rootPolynomial n rightIndex) ∣
      value vertex - value (vertex * rootReflection rightIndex)
    have hassociated := _root_.Schubert.DihedralSplines.IndexedDD.associated_of_endpoint
      n vertex rightIndex index hendpoint
    rw [hendpoint]
    exact hassociated.dvd_iff_dvd_left.mpr (hvalue vertex index)

end Schubert.DihedralSplines
