import DihedralHessenberg.Paper.BlockTransport
import DihedralHessenberg.Paper.FlowupBoundary
import DihedralHessenberg.Paper.UpperBlockSelected
import DihedralHessenberg.Paper.HessenbergTopEdge

/-! # Alternating-block supports of recursive flow-up splines -/

noncomputable section

namespace Schubert.DihedralSplines.FlowupSpline

open Schubert.Dihedral
open scoped Classical

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- Every selected high-half vector is a boundary-degree spline on a selected block. -/
theorem high_block (vertex : DihedralGroup n) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (hascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1)
    (hhalf : n < 2 * length n hthree vertex + 1)
    (hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges) :
    ∃ block : HessenbergIdeal.Block ideal, block.base = vertex ∧
      (ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
        block.base).card = ideal.toRootSubset.length vertex ∧
      ∀ current, (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current ≠ 0 ↔
        current ∈ block.vertices := by
  obtain ⟨block, hbase, _, hvertices⟩ :=
    ideal.ascent_block alpha hsimple vertex hascent hhalf hedge
  refine ⟨block, hbase, ?_, ?_⟩
  · rw [hvertices, hbase, ideal.toRootSubset.boundaryRoots_card]
    let upper := HessenbergIdeal.Upper.ofAscent ideal alpha hsimple vertex hascent hhalf hedge
    exact upper.boundary_card vertex (bruhatLE_refl n hthree vertex)
  · intro current
    rw [support_high ideal vertex alpha hsimple hascent hhalf hedge current]
    change BruhatLE n hthree vertex current ↔
      current ∈ (block.vertices : Set (DihedralGroup n))
    rw [hvertices]
    rfl

/-- Every vector is Schubert, the given top, or localized on a selected block. -/
theorem block_shape (vertex : DihedralGroup n) :
    spline ideal vertex = ideal.toRootSubset.restrictFull (SchubertSpline.spline n hthree vertex) ∨
      vertex = longestElement n hthree ∨
      ∃ block : HessenbergIdeal.Block ideal, block.base = vertex ∧
        (ideal.toRootSubset.boundaryRoots (block.vertices : Set (DihedralGroup n))
          block.base).card = ideal.toRootSubset.length vertex ∧
        ∀ current, (spline ideal vertex : DihedralGroup n → CoordinatePolynomial) current ≠ 0 ↔
          current ∈ block.vertices := by
  generalize hmeasure : n - length n hthree vertex = measure
  induction measure using Nat.strong_induction_on generalizing vertex with
  | h measure ih =>
    by_cases hidentity : vertex = 1
    · subst vertex
      left
      rw [spline_one, SchubertSpline.spline_one]
      rfl
    by_cases htop : vertex = longestElement n hthree
    · exact Or.inr (Or.inl htop)
    let alpha := SchubertSpline.ascentRoot n hthree vertex hidentity htop
    have hsimple := (SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop).1
    have hascent := (SchubertSpline.ascentRoot_spec n hthree vertex hidentity htop).2
    change (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) at hsimple
    change length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1 at hascent
    by_cases hedge : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges
    · by_cases hhalf : 2 * length n hthree vertex + 1 ≤ n
      · exact Or.inl (spline_low ideal vertex hidentity htop alpha hsimple hascent hedge hhalf)
      · exact Or.inr (Or.inr (high_block ideal vertex alpha hsimple hascent (by omega) hedge))
    · have hup : BruhatLE n hthree vertex (alpha.reflection * vertex) :=
        bruhatLE_of_length_lt n hthree (by omega)
      have hne : vertex ≠ alpha.reflection * vertex := by
        intro heq
        have := congrArg (length n hthree) heq
        omega
      have hdegree : ideal.toRootSubset.length (alpha.reflection * vertex) =
          ideal.toRootSubset.length vertex := by
        change (ideal.toRootSubset.inversions (alpha.reflection * vertex)).ncard =
          (ideal.toRootSubset.inversions vertex).ncard
        rw [ideal.inversions_no_edge alpha hsimple vertex hup hne hedge]
      have hbound := length_le_polygon_parameter n hthree (alpha.reflection * vertex)
      have hless : n - length n hthree (alpha.reflection * vertex) < measure := by omega
      obtain hschubert | htailTop | ⟨block, hbase, hcard, hsupport⟩ :=
        ih _ hless (alpha.reflection * vertex) rfl
      · have hdegreeSchubert := congrArg ideal.toRootSubset.degree hschubert
        rw [degree] at hdegreeSchubert
        have hrestricted : ideal.toRootSubset.degree
            (ideal.toRootSubset.restrictFull
              (SchubertSpline.spline n hthree (alpha.reflection * vertex))) =
                length n hthree (alpha.reflection * vertex) := by
          change (RootSubset.full n).degree
            (SchubertSpline.spline n hthree (alpha.reflection * vertex)) = _
          exact ((SchubertSpline.construct n hthree (alpha.reflection * vertex)).degree_eq).trans
            (RootSubset.length_full n hthree (alpha.reflection * vertex))
        rw [hrestricted, hdegree] at hdegreeSchubert
        have hdegreeBound : ideal.toRootSubset.length vertex ≤ length n hthree vertex := by
          rw [ideal.length_indexed]
          exact ideal.indexed.length_le_coxeter_length vertex
        omega
      · exact (hedge (ideal.edge_to_top alpha hsimple vertex hascent htailTop)).elim
      · right
        right
        refine ⟨block.translate alpha.reflection, ?_, ?_, ?_⟩
        · change alpha.reflection * block.base = vertex
          rw [hbase, ← mul_assoc, alpha.reflection_square, one_mul]
        · rw [block.translate_degree, hcard, hdegree]
        · intro current
          rw [spline_no_edge ideal vertex hidentity htop alpha hsimple hascent hedge]
          have hdot := ideal.toRootSubset.dot_support hthree alpha.reflection
            (alpha.reflection⁻¹ * current) (spline ideal (alpha.reflection * vertex))
          rw [mul_inv_cancel_left] at hdot
          rw [hdot, hsupport]
          change alpha.reflection⁻¹ * current ∈ block.vertices ↔
            current ∈ ((block.translate alpha.reflection).vertices : Set (DihedralGroup n))
          rw [block.translate_vertices]
          constructor
          · intro hinside
            exact ⟨alpha.reflection⁻¹ * current, hinside, mul_inv_cancel_left _ _⟩
          · rintro ⟨original, horiginal, rfl⟩
            simpa only [inv_mul_cancel_left, Finset.mem_coe] using horiginal

end Schubert.DihedralSplines.FlowupSpline
