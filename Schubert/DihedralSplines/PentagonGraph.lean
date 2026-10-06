import Schubert.DihedralSplines.DiagramTable
import Schubert.Dihedral.RootAngularEquality
import Mathlib.Tactic

/-! # The fifteen-edge pentagon diagram -/

noncomputable section
namespace Schubert.DihedralSplines
open Schubert.Dihedral
namespace Pentagon

/-- The three selected positive vectors. -/
def selected : RootSubset 5 where
  carrier := {positiveRoot 5 0, positiveRoot 5 1, positiveRoot 5 2}
  positive := by
    rintro vector (rfl | rfl | rfl)
    all_goals exact ⟨_, rfl⟩

/-- The ten vertices in their displayed word order. -/
def vertices : Fin 10 → DihedralGroup 5 :=
  let first := (simpleRoot 5 (by decide) 0).reflection
  let second := (simpleRoot 5 (by decide) 1).reflection
  ![1, second, first, first * second, second * first, second * first * second,
    first * second * first, (first * second)^2, (second * first)^2,
    (first * second)^2 * first]

/-- Oriented representatives of the fifteen undirected edges. -/
def pairs : Fin 15 → DihedralGroup 5 × DihedralGroup 5 :=
  ![(vertices 0, vertices 1),
    (vertices 1, vertices 4),
    (vertices 4, vertices 5),
    (vertices 5, vertices 8),
    (vertices 8, vertices 9),
    (vertices 7, vertices 9),
    (vertices 6, vertices 7),
    (vertices 3, vertices 6),
    (vertices 2, vertices 3),
    (vertices 0, vertices 2),
    (vertices 0, vertices 6),
    (vertices 1, vertices 8),
    (vertices 2, vertices 4),
    (vertices 3, vertices 9),
    (vertices 5, vertices 7)]

private def normalIndex : Fin 15 → Fin 5 := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 2, 2, 2, 2]
private def normal (row : Fin 15) : PositiveRoot 5 := positiveRootEquiv 5 (normalIndex row)
private def labelIndex : Fin 15 → Fin 5 := ![1, 3, 4, 2, 0, 1, 3, 4, 2, 0, 2, 4, 1, 3, 0]

/-- The positive vector labels. -/
def labels (row : Fin 15) : RealPlane := positiveRoot 5 (labelIndex row)

/-- Each pair is joined by its selected reflection. -/
theorem endpoints (row : Fin 15) :
    (pairs row).2 = (pairs row).1 * (normal row).reflection := by
  fin_cases row <;>
    norm_num [pairs, vertices, normal, normalIndex, simpleRoot_reflection,
      simpleReflection, firstSimpleReflection, secondSimpleReflection,
      PositiveRoot.reflection_equiv, rootReflection_eq_sr, reflectionCoordinate,
      DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
      DihedralGroup.r_mul_r, DihedralGroup.r_zero, pow_two]
  all_goals decide

private theorem rotation_image (coordinate : ZMod 5) (index image : Fin 5)
    (hangle : ((angularIndex index + 2 * coordinate.val : ℕ) : ℤ) % 10 =
      angularIndex image) :
    realAction 5 (.r coordinate) (positiveRoot 5 index) = positiveRoot 5 image := by
  apply complexify_injective
  rw [realAction_complexify 5 _ _ (Or.inl ⟨index, rfl⟩)]
  change vectorOperator 5 (.r coordinate) (complexPositiveRoot 5 index) = _
  rw [vectorOperator_r_complexPositiveRoot]
  apply congrArg complexify
  apply (unitRootAt_int_eq_positiveRoot_iff 5 _ image).mpr at hangle
  simpa only [Int.cast_natCast] using hangle

private theorem reflection_image (coordinate : ZMod 5) (index image : Fin 5)
    (hangle : (5 - angularIndex index - 2 * coordinate.val : ℤ) % 10 =
      angularIndex image) :
    realAction 5 (.sr coordinate) (positiveRoot 5 index) = positiveRoot 5 image := by
  apply complexify_injective
  rw [realAction_complexify 5 _ _ (Or.inl ⟨index, rfl⟩)]
  change vectorOperator 5 (.sr coordinate) (complexPositiveRoot 5 index) = _
  rw [vectorOperator_sr_complexPositiveRoot]
  exact congrArg complexify ((unitRootAt_int_eq_positiveRoot_iff 5 _ image).mpr hangle)

/-- Every generator has exactly the listed unit-root label. -/
theorem root_labels (row : Fin 15) :
    realAction 5 (pairs row).1 (normal row).val = labels row := by
  fin_cases row <;>
    norm_num only [pairs, vertices, normal, normalIndex, labels, labelIndex,
      positiveRootEquiv_val, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
      DihedralGroup.r_zero, pow_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  · change realAction 5 (.r 0) (positiveRoot 5 1) = positiveRoot 5 1
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 1) (positiveRoot 5 0) = positiveRoot 5 3
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.r 4) (positiveRoot 5 1) = positiveRoot 5 4
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 2) (positiveRoot 5 0) = positiveRoot 5 2
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.r 3) (positiveRoot 5 1) = positiveRoot 5 0
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.r 2) (positiveRoot 5 0) = positiveRoot 5 1
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 4) (positiveRoot 5 1) = positiveRoot 5 3
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.r 1) (positiveRoot 5 0) = positiveRoot 5 4
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 0) (positiveRoot 5 1) = positiveRoot 5 2
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.r 0) (positiveRoot 5 0) = positiveRoot 5 0
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.r 0) (positiveRoot 5 2) = positiveRoot 5 2
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 1) (positiveRoot 5 2) = positiveRoot 5 4
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.sr 0) (positiveRoot 5 2) = positiveRoot 5 1
    exact reflection_image _ _ _ (by decide)
  · change realAction 5 (.r 1) (positiveRoot 5 2) = positiveRoot 5 3
    exact rotation_image _ _ _ (by decide)
  · change realAction 5 (.sr 2) (positiveRoot 5 2) = positiveRoot 5 0
    exact reflection_image _ _ _ (by decide)

/-- Every listed pair is a selected edge. -/
theorem edge_mem (row : Fin 15) : pairs row ∈ selected.edges := by
  refine ⟨normal row, ?_, endpoints row⟩
  change positiveRoot 5 (normalIndex row) ∈ selected.carrier
  fin_cases row <;> simp [normalIndex, selected]

/-- The fifteen pairs and their reversals exhaust the selected graph. -/
theorem edges (pair : DihedralGroup 5 × DihedralGroup 5) :
    pair ∈ selected.edges ↔ ∃ row : Fin 15, pair = pairs row ∨ pair = (pairs row).swap := by
  rcases pair with ⟨source, target⟩
  constructor
  · rintro ⟨alpha, hselected, htarget⟩
    change alpha.val = positiveRoot 5 0 ∨ alpha.val = positiveRoot 5 1 ∨
      alpha.val = positiveRoot 5 2 at hselected
    have halpha : alpha = positiveRootEquiv 5 0 ∨ alpha = positiveRootEquiv 5 1 ∨
        alpha = positiveRootEquiv 5 2 :=
      hselected.imp Subtype.ext (fun h => h.imp Subtype.ext Subtype.ext)
    rcases halpha with rfl | rfl | rfl
    all_goals dsimp only at htarget
    all_goals subst target
    all_goals cases source with
    | r coordinate =>
      fin_cases coordinate <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, PositiveRoot.reflection_equiv,
          rootReflection_eq_sr, reflectionCoordinate, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero, pow_two]
      all_goals decide
    | sr coordinate =>
      fin_cases coordinate <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, PositiveRoot.reflection_equiv,
          rootReflection_eq_sr, reflectionCoordinate, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero, pow_two]
      all_goals decide
  · rintro ⟨row, heq | heq⟩
    · exact heq ▸ edge_mem row
    · exact heq ▸ (selected.reverse ⟨pairs row, edge_mem row⟩).property

/-- The listed edge generators are exactly the forms of the displayed root vectors. -/
theorem edge_labels (row : Fin 15) :
    selected.edgeLabel ⟨pairs row, edge_mem row⟩ =
      linearPolynomial (complexify (labels row)) := by
  rw [RootSubset.edgeLabel]
  have hnormal := selected.edgeRoot_unique ⟨pairs row, edge_mem row⟩ (normal row) (endpoints row)
  rw [hnormal]
  change linearPolynomial (complexify (realAction 5 (pairs row).1 (normal row).val)) = _
  rw [root_labels]

end Pentagon
end Schubert.DihedralSplines
