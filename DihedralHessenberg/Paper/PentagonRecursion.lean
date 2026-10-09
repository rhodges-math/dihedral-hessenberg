import DihedralHessenberg.Paper.PentagonFamily
import DihedralHessenberg.Paper.FlowupEquations

/-! # The pentagon generators are the recursively constructed flow-up splines

For `n = 5` and `H = {α₁, α₂, α₃}`, each of the ten displayed generators is the flow-up spline
`ρ_w` produced by the recursive construction of the flow-up basis theorem at its vertex `w`:
the construction follows the simple ascent of `w`, and at each vertex its step (a divided
difference, a dot translation or a restricted Schubert spline) is the displayed one.
-/

noncomputable section
namespace Schubert.DihedralSplines.Pentagon
open Schubert.Dihedral

private theorem first_reflection : (simpleRoot 5 (by decide) 0).reflection = .sr 0 := by
  rw [simpleRoot_reflection]
  rfl

private theorem second_reflection : (simpleRoot 5 (by decide) 1).reflection = .sr 1 := by
  rw [simpleRoot_reflection]
  rfl

/-- The ten vertices as rotations and reflections. -/
private def vertexTable : Fin 10 → DihedralGroup 5 :=
  ![.r 0, .sr 1, .sr 0, .r 1, .r 4, .sr 2, .sr 4, .r 2, .r 3, .sr 3]

private theorem vertices_eq : vertices = vertexTable := by
  funext row
  fin_cases row <;>
    simp [vertices, vertexTable, first_reflection, second_reflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.r_mul_r, pow_two] <;>
    decide

private theorem ne_one (row : Fin 10) (hrow : row ≠ 0) : vertices row ≠ 1 := by
  rw [vertices_eq]
  revert row
  decide

private theorem ne_top (row : Fin 10) (hrow : row ≠ 9) :
    vertices row ≠ longestElement 5 (by decide) := by
  rw [← last_vertex, vertices_eq]
  revert row
  decide

/-- A pair that is neither a listed edge nor the reversal of one is not an edge. -/
private theorem not_edge {source target : DihedralGroup 5}
    (hnot : ∀ row : Fin 15, (source, target) ≠ pairs row ∧ (source, target) ≠ (pairs row).swap) :
    (source, target) ∉ ideal.toRootSubset.edges := by
  intro hedge
  obtain ⟨row, heq | heq⟩ := (edges _).mp hedge
  · exact (hnot row).1 heq
  · exact (hnot row).2 heq

/-- The recursive spline at the last displayed vertex is the top certificate. -/
private theorem spline_top_vertex : FlowupSpline.spline ideal (vertices 9) = top.value := by
  rw [top_value, last_vertex, FlowupSpline.spline_top]

private theorem spline_eight : FlowupSpline.spline ideal (vertices 8) = afterFirst.value := by
  have hstep : (simpleRoot 5 (by decide) 0).reflection * vertices 8 = vertices 9 := by
    rw [first_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_high ideal (vertices 8) (ne_one 8 (by decide)) (ne_top 8 (by decide))
    (simpleRoot 5 (by decide) 0) (Or.inl rfl) (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; exact edge_mem 4) (by rw [word_lengths]; decide), afterFirst_value]
  symm
  apply ideal.dividedDifference_unique
  intro vertex
  rw [hstep, spline_top_vertex]
  exact ideal.dividedDifference_mul _ _ _ vertex

private theorem spline_seven : FlowupSpline.spline ideal (vertices 7) = afterSecond.value := by
  have hstep : (simpleRoot 5 (by decide) 1).reflection * vertices 7 = vertices 9 := by
    rw [second_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_high ideal (vertices 7) (ne_one 7 (by decide)) (ne_top 7 (by decide))
    (simpleRoot 5 (by decide) 1) (Or.inr rfl) (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; exact edge_mem 5) (by rw [word_lengths]; decide), afterSecond_value]
  symm
  apply ideal.dividedDifference_unique
  intro vertex
  rw [hstep, spline_top_vertex]
  exact ideal.dividedDifference_mul _ _ _ vertex

private theorem spline_five : FlowupSpline.spline ideal (vertices 5) = afterBoth.value := by
  have hstep : (simpleRoot 5 (by decide) 0).reflection * vertices 5 = vertices 7 := by
    rw [first_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_high ideal (vertices 5) (ne_one 5 (by decide)) (ne_top 5 (by decide))
    (simpleRoot 5 (by decide) 0) (Or.inl rfl) (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; exact edge_mem 14) (by rw [word_lengths]; decide), afterBoth_value]
  symm
  apply ideal.dividedDifference_unique
  intro vertex
  rw [hstep, spline_seven]
  exact ideal.dividedDifference_mul _ _ _ vertex

private theorem spline_six : FlowupSpline.spline ideal (vertices 6) = leftMiddle.value := by
  have hstep : (simpleRoot 5 (by decide) 1).reflection * vertices 6 = vertices 8 := by
    rw [second_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_no_edge ideal (vertices 6) (ne_one 6 (by decide))
    (ne_top 6 (by decide)) (simpleRoot 5 (by decide) 1) (Or.inr rfl)
    (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; apply not_edge; simp only [pairs, vertices_eq]; decide),
    hstep, spline_eight, leftMiddle_value]

private theorem spline_four : FlowupSpline.spline ideal (vertices 4) = rightMiddle.value := by
  have hstep : (simpleRoot 5 (by decide) 0).reflection * vertices 4 = vertices 6 := by
    rw [first_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_no_edge ideal (vertices 4) (ne_one 4 (by decide))
    (ne_top 4 (by decide)) (simpleRoot 5 (by decide) 0) (Or.inl rfl)
    (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; apply not_edge; simp only [pairs, vertices_eq]; decide),
    hstep, spline_six, rightMiddle_value]

private theorem spline_three : FlowupSpline.spline ideal (vertices 3) = leftLow.value := by
  have hstep : (simpleRoot 5 (by decide) 1).reflection * vertices 3 = vertices 5 := by
    rw [second_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_no_edge ideal (vertices 3) (ne_one 3 (by decide))
    (ne_top 3 (by decide)) (simpleRoot 5 (by decide) 1) (Or.inr rfl)
    (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; apply not_edge; simp only [pairs, vertices_eq]; decide),
    hstep, spline_five, leftLow_value]

private theorem spline_one_row : FlowupSpline.spline ideal (vertices 1) = rightLow.value := by
  have hstep : (simpleRoot 5 (by decide) 0).reflection * vertices 1 = vertices 3 := by
    rw [first_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_no_edge ideal (vertices 1) (ne_one 1 (by decide))
    (ne_top 1 (by decide)) (simpleRoot 5 (by decide) 0) (Or.inl rfl)
    (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; apply not_edge; simp only [pairs, vertices_eq]; decide),
    hstep, spline_three, rightLow_value]

private theorem spline_two : FlowupSpline.spline ideal (vertices 2) = (generator 2).value := by
  have hstep : (simpleRoot 5 (by decide) 1).reflection * vertices 2 = vertices 4 := by
    rw [second_reflection, vertices_eq]
    decide
  rw [FlowupSpline.spline_low ideal (vertices 2) (ne_one 2 (by decide)) (ne_top 2 (by decide))
    (simpleRoot 5 (by decide) 1) (Or.inr rfl) (by rw [hstep, word_lengths, word_lengths]; decide)
    (by rw [hstep]; exact edge_mem 12) (by rw [word_lengths]; decide), initial_formulas.2]
  rfl

/-- Each displayed pentagon generator is the flow-up spline constructed at its vertex. -/
theorem generator_eq_spline (row : Fin 10) :
    (generator row).value = FlowupSpline.spline ideal (vertices row) := by
  fin_cases row
  · exact initial_formulas.1.trans (FlowupSpline.spline_one ideal).symm
  · exact spline_one_row.symm
  · exact spline_two.symm
  · exact spline_three.symm
  · exact spline_four.symm
  · exact spline_five.symm
  · exact spline_six.symm
  · exact spline_seven.symm
  · exact spline_eight.symm
  · exact spline_top_vertex.symm

end Schubert.DihedralSplines.Pentagon
