import Schubert.DihedralSplines.TriangleCayley

/-! # The labelled eight-edge Cayley graph of the square -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem square_first_real (vector : RealPlane) :
    realAction 4 (simpleRoot 4 (by decide) 0).reflection vector = ![-vector 0, vector 1] := by
  funext coordinate
  fin_cases coordinate <;> simp [realAction, square_first_action, complexify]

private theorem square_second_real (vector : RealPlane) :
    realAction 4 (simpleRoot 4 (by decide) 1).reflection vector = ![vector 1, vector 0] := by
  funext coordinate
  fin_cases coordinate <;> simp [realAction, square_second_action, complexify]

namespace Square

/-- The square diagram selects precisely the two simple roots. -/
def selected : RootSubset 4 where
  carrier := {(simpleRoot 4 (by decide) 0).val, (simpleRoot 4 (by decide) 1).val}
  positive := by
    rintro vector (rfl | rfl)
    · exact (simpleRoot 4 (by decide) 0).property
    · exact (simpleRoot 4 (by decide) 1).property

private def vertices : Fin 8 → DihedralGroup 4 :=
  let first := (simpleRoot 4 (by decide) 0).reflection
  let second := (simpleRoot 4 (by decide) 1).reflection
  ![1, second, first, first * second, second * first, second * first * second,
    first * second * first, first * second * first * second]

/-- The eight displayed oriented representatives of the undirected square edges. -/
def pairs : Fin 8 → DihedralGroup 4 × DihedralGroup 4 :=
  ![(vertices 0, vertices 1), (vertices 0, vertices 2), (vertices 1, vertices 4),
    (vertices 2, vertices 3), (vertices 3, vertices 6), (vertices 4, vertices 5),
    (vertices 5, vertices 7), (vertices 6, vertices 7)]

private def normal : Fin 8 → PositiveRoot 4 :=
  let first := simpleRoot 4 (by decide) 0
  let second := simpleRoot 4 (by decide) 1
  ![second, first, first, second, first, second, first, second]

/-- The edge labels of the square diagram. -/
def labels : Fin 8 → CoordinatePolynomial :=
  let factor := MvPolynomial.C ((Real.sqrt 2 / 2 : ℝ) : ℂ)
  let x := MvPolynomial.X (0 : Fin 2)
  let y := MvPolynomial.X (1 : Fin 2)
  ![factor * (-x + y), x, y, factor * (x + y), y,
    factor * (x + y), x, factor * (-x + y)]

/-- The selected reflection normal joins each listed square pair. -/
theorem endpoints (row : Fin 8) :
    (pairs row).2 = (pairs row).1 * (normal row).reflection := by
  fin_cases row <;>
    norm_num [pairs, normal, vertices, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
      DihedralGroup.r_zero]
  all_goals decide

/-- Every listed square pair belongs to the selected graph. -/
theorem edge_mem (row : Fin 8) : pairs row ∈ selected.edges := by
  refine ⟨normal row, ?_, endpoints row⟩
  change (normal row).val ∈ selected.carrier
  fin_cases row <;> simp [selected, normal]

/-- The listed square pairs and their reversals are the entire selected graph. -/
theorem edges (pair : DihedralGroup 4 × DihedralGroup 4) :
    pair ∈ selected.edges ↔ ∃ row : Fin 8, pair = pairs row ∨ pair = (pairs row).swap := by
  rcases pair with ⟨source, target⟩
  constructor
  · rintro ⟨alpha, hselected, htarget⟩
    change alpha.val = (simpleRoot 4 (by decide) 0).val ∨
      alpha.val = (simpleRoot 4 (by decide) 1).val at hselected
    have halpha : alpha = simpleRoot 4 (by decide) 0 ∨
        alpha = simpleRoot 4 (by decide) 1 :=
      hselected.imp Subtype.ext Subtype.ext
    rcases halpha with rfl | rfl
    all_goals change target = source * (simpleRoot 4 (by decide) _).reflection at htarget
    all_goals subst target
    all_goals cases source with
    | r coordinate =>
      fin_cases coordinate <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero]
      all_goals decide
    | sr coordinate =>
      fin_cases coordinate <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero]
      all_goals decide
  · rintro ⟨row, heq | heq⟩
    · exact heq ▸ edge_mem row
    · exact heq ▸ (selected.reverse ⟨pairs row, edge_mem row⟩).property

/-- The eight square edges have exactly their listed labels. -/
theorem edge_labels (row : Fin 8) :
    selected.edgeLabel ⟨pairs row, edge_mem row⟩ = labels row := by
  rw [RootSubset.edgeLabel]
  have hnormal := selected.edgeRoot_unique ⟨pairs row, edge_mem row⟩ (normal row) (endpoints row)
  rw [hnormal]
  have hzero : (simpleRoot 4 (by decide) 0).val = ![1, 0] := by
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
    simp [unitRootAt]
  fin_cases row
  case' «0» =>
    change linearPolynomial (complexify (realAction 4 (1) ((simpleRoot 4 (by decide) 1).val))) =
      labels 0
  case' «1» =>
    change linearPolynomial (complexify (realAction 4 (1) ((simpleRoot 4 (by decide) 0).val))) =
      labels 1
  case' «2» =>
    change linearPolynomial (complexify (realAction 4 ((simpleRoot 4 (by decide) 1).reflection)
      ((simpleRoot 4 (by decide) 0).val))) = labels 2
  case' «3» =>
    change linearPolynomial (complexify (realAction 4 ((simpleRoot 4 (by decide) 0).reflection)
      ((simpleRoot 4 (by decide) 1).val))) = labels 3
  case' «4» =>
    change linearPolynomial (complexify (realAction 4 (((simpleRoot 4 (by decide) 0).reflection *
      (simpleRoot 4 (by decide) 1).reflection)) ((simpleRoot 4 (by decide) 0).val))) = labels 4
  case' «5» =>
    change linearPolynomial (complexify (realAction 4 (((simpleRoot 4 (by decide) 1).reflection *
      (simpleRoot 4 (by decide) 0).reflection)) ((simpleRoot 4 (by decide) 1).val))) = labels 5
  case' «6» =>
    change linearPolynomial (complexify (realAction 4 (((simpleRoot 4 (by decide) 1).reflection *
      (simpleRoot 4 (by decide) 0).reflection * (simpleRoot 4 (by decide) 1).reflection))
      ((simpleRoot 4 (by decide) 0).val))) = labels 6
  case' «7» =>
    change linearPolynomial (complexify (realAction 4 (((simpleRoot 4 (by decide) 0).reflection *
      (simpleRoot 4 (by decide) 1).reflection * (simpleRoot 4 (by decide) 0).reflection))
      ((simpleRoot 4 (by decide) 1).val))) = labels 7
  all_goals simp only [realAction_one, id_eq, realAction_mul_plane, square_first_real,
    square_second_real, hzero, square_second_vector, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals norm_num [labels, linearPolynomial, complexify]
  all_goals have hnegative : -((Real.sqrt 2 : ℝ) : ℂ) / 2 =
      -(((Real.sqrt 2 : ℝ) : ℂ) / 2) := by ring
  all_goals rw [hnegative, map_neg]
  all_goals ring

end Square
end Schubert.DihedralSplines
