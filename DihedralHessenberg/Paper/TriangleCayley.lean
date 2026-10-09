import DihedralHessenberg.Paper.SquareAction
import DihedralHessenberg.Paper.SquareLabels
import DihedralHessenberg.Dihedral.RootInversionSets
import DihedralHessenberg.Dihedral.FaithfulRealization
import DihedralHessenberg.Dihedral.UnitDirections
import Mathlib.Tactic

/-! # Exact labeled triangle Cayley diagrams -/

noncomputable section

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem triangle_first (vector : RealPlane) :
    realAction 3 (simpleRoot 3 (by decide) 0).reflection vector = ![-vector 0, vector 1] := by
  rw [PositiveRoot.realAction_reflection]
  have hnormal : (simpleRoot 3 (by decide) 0).val = ![1, 0] := by
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
    simp [unitRootAt]
  rw [hnormal]
  apply realPlane_ext <;> simp [realBilinearForm]
  all_goals ring

private theorem triangle_second (vector : RealPlane) :
    realAction 3 (simpleRoot 3 (by decide) 1).reflection vector =
      ![vector 0 / 2 + Real.sqrt 3 * vector 1 / 2,
        Real.sqrt 3 * vector 0 / 2 - vector 1 / 2] := by
  rw [PositiveRoot.realAction_reflection]
  have hnormal : (simpleRoot 3 (by decide) 1).val = ![-1 / 2, Real.sqrt 3 / 2] := by
    rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
    simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three, neg_div]
  rw [hnormal]
  apply realPlane_ext <;> simp only [realBilinearForm, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  · ring
  · ring_nf
    norm_num [Real.sq_sqrt]
    ring

namespace Triangle

/-- All positive triangle unit roots are selected. -/
def selected : RootSubset 3 := ⟨positiveRoots 3, fun _ hmem => hmem⟩

private def vertices : Fin 6 → DihedralGroup 3 :=
  let first := (simpleRoot 3 (by decide) 0).reflection
  let second := (simpleRoot 3 (by decide) 1).reflection
  ![1, second, first, first * second, second * first, first * second * first]

/-- The nine displayed oriented representatives of the undirected triangle edges. -/
def pairs : Fin 9 → DihedralGroup 3 × DihedralGroup 3 :=
  ![(vertices 0, vertices 1), (vertices 0, vertices 2), (vertices 1, vertices 4),
    (vertices 2, vertices 3), (vertices 3, vertices 5), (vertices 4, vertices 5),
    (vertices 0, vertices 5), (vertices 3, vertices 1), (vertices 4, vertices 2)]

private def normal : Fin 9 → PositiveRoot 3 :=
  let first := simpleRoot 3 (by decide) 0
  let second := simpleRoot 3 (by decide) 1
  let third := positiveRootEquiv 3 ⟨2, by decide⟩
  ![second, first, first, second, first, second, third, third, third]

/-- The nine signed root labels of the triangle diagram. -/
def labels : Fin 9 → RealPlane :=
  let first := (simpleRoot 3 (by decide) 0).val
  let second := (simpleRoot 3 (by decide) 1).val
  let third := positiveRoot 3 ⟨2, by decide⟩
  ![second, first, third, third, second, first, third, -first, -second]

/-- The selected reflection normal joins each listed pair. -/
theorem endpoints (row : Fin 9) :
    (pairs row).2 = (pairs row).1 * (normal row).reflection := by
  fin_cases row <;>
    norm_num [pairs, normal, vertices, simpleRoot_reflection, simpleReflection,
      firstSimpleReflection, secondSimpleReflection, PositiveRoot.reflection_equiv,
      rootReflection, rotation, DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r, DihedralGroup.r_zero]
  all_goals decide

/-- Each root image is exactly the corresponding signed diagram label. -/
theorem root_labels (row : Fin 9) :
    realAction 3 (pairs row).1 (normal row).val = labels row := by
  have hzero : (simpleRoot 3 (by decide) 0).val = ![1, 0] := by
    rw [simpleRoot_zero, positiveRootEquiv_val, positiveRoot, rootAngle_first]
    simp [unitRootAt]
  have hone : (simpleRoot 3 (by decide) 1).val = ![-1 / 2, Real.sqrt 3 / 2] := by
    rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
    simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_three, Real.sin_pi_div_three, neg_div]
  have htwo : positiveRoot 3 ⟨2, by decide⟩ = ![1 / 2, Real.sqrt 3 / 2] := by
    norm_num [positiveRoot, rootAngle, unitRootAt, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
  fin_cases row
  case' «0» =>
    change realAction 3 (1) ((simpleRoot 3 (by decide) 1).val) = (simpleRoot 3 (by decide) 1).val
  case' «1» =>
    change realAction 3 (1) ((simpleRoot 3 (by decide) 0).val) = (simpleRoot 3 (by decide) 0).val
  case' «2» =>
    change realAction 3 ((simpleRoot 3 (by decide) 1).reflection) ((simpleRoot 3 (by decide)
      0).val) = positiveRoot 3 ⟨2, by decide⟩
  case' «3» =>
    change realAction 3 ((simpleRoot 3 (by decide) 0).reflection) ((simpleRoot 3 (by decide)
      1).val) = positiveRoot 3 ⟨2, by decide⟩
  case' «4» =>
    change realAction 3 (((simpleRoot 3 (by decide) 0).reflection * (simpleRoot 3 (by decide)
      1).reflection)) ((simpleRoot 3 (by decide) 0).val) = (simpleRoot 3 (by decide) 1).val
  case' «5» =>
    change realAction 3 (((simpleRoot 3 (by decide) 1).reflection * (simpleRoot 3 (by decide)
      0).reflection)) ((simpleRoot 3 (by decide) 1).val) = (simpleRoot 3 (by decide) 0).val
  case' «6» =>
    change realAction 3 (1) (positiveRoot 3 ⟨2, by decide⟩) = positiveRoot 3 ⟨2, by decide⟩
  case' «7» =>
    change realAction 3 ((simpleRoot 3 (by decide) 0).reflection *
      (simpleRoot 3 (by decide) 1).reflection) (positiveRoot 3 ⟨2, by decide⟩) = -((simpleRoot 3
        (by decide) 0).val)
  case' «8» =>
    change realAction 3 ((simpleRoot 3 (by decide) 1).reflection *
      (simpleRoot 3 (by decide) 0).reflection) (positiveRoot 3 ⟨2, by decide⟩) = -((simpleRoot 3
        (by decide) 1).val)
  all_goals simp only [realAction_one, id_eq, realAction_mul_plane, triangle_first,
    triangle_second, hzero, hone, htwo, Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals apply realPlane_ext
  all_goals simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  all_goals (try ring_nf)
  all_goals norm_num [Real.sq_sqrt]

/-- Every listed triangle pair belongs to the selected graph. -/
theorem edge_mem (row : Fin 9) : pairs row ∈ selected.edges :=
  ⟨normal row, (normal row).property, endpoints row⟩

/-- The listed triangle pairs and their reversals are the entire selected graph. -/
theorem edges (pair : DihedralGroup 3 × DihedralGroup 3) :
    pair ∈ selected.edges ↔ ∃ row : Fin 9, pair = pairs row ∨ pair = (pairs row).swap := by
  rcases pair with ⟨source, target⟩
  constructor
  · rintro ⟨alpha, _, htarget⟩
    obtain ⟨index, rfl⟩ := (positiveRootEquiv 3).surjective alpha
    change target = source * ((positiveRootEquiv 3) index).reflection at htarget
    subst target
    cases source with
    | r coordinate =>
      fin_cases coordinate <;> fin_cases index <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, PositiveRoot.reflection_equiv,
          rootReflection_eq_sr, reflectionCoordinate, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero]
      all_goals decide
    | sr coordinate =>
      fin_cases coordinate <;> fin_cases index <;>
        norm_num [pairs, vertices, simpleRoot_reflection, simpleReflection,
          firstSimpleReflection, secondSimpleReflection, PositiveRoot.reflection_equiv,
          rootReflection_eq_sr, reflectionCoordinate, DihedralGroup.sr_mul_sr,
          DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
          DihedralGroup.r_zero]
      all_goals decide
  · rintro ⟨row, heq | heq⟩
    · exact heq ▸ edge_mem row
    · exact heq ▸ (selected.reverse ⟨pairs row, edge_mem row⟩).property

/-- The nine diagram edges have exactly their listed root-form generators. -/
theorem edge_labels (row : Fin 9) :
    selected.edgeLabel ⟨pairs row, edge_mem row⟩ =
      linearPolynomial (complexify (labels row)) := by
  rw [RootSubset.edgeLabel]
  have hnormal := selected.edgeRoot_unique ⟨pairs row, edge_mem row⟩ (normal row) (endpoints row)
  rw [hnormal]
  change linearPolynomial (complexify (realAction 3 (pairs row).1 (normal row).val)) = _
  rw [root_labels]

private theorem numbered_inversions (index : Fin 3) :
    positiveRoot 3 index ∈ selected.inversions
      ((simpleRoot 3 (by decide) 1).reflection * (simpleRoot 3 (by decide) 0).reflection) ↔
      index = 0 ∨ index = 2 := by
  rw [RootSubset.inversions, Set.mem_inter_iff, mem_rightInversionSet 3 (by decide)]
  have hselected : positiveRoot 3 index ∈ selected.carrier := ⟨index, rfl⟩
  rw [and_iff_right hselected]
  have hword : (simpleRoot 3 (by decide) 1).reflection *
      (simpleRoot 3 (by decide) 0).reflection = DihedralGroup.r (-1 : ZMod 3) := by
    norm_num [simpleRoot_reflection, simpleReflection, firstSimpleReflection,
      secondSimpleReflection, DihedralGroup.sr_mul_sr]
  rw [hword, mem_rightInversions_r_iff]
  fin_cases index <;> norm_num [angularIndex, ZMod.neg_val', ZMod.val_one_eq_one_mod]

/-- The triangle example has exactly its two stated positive inversion vectors. -/
theorem inversions : selected.inversions
    ((simpleRoot 3 (by decide) 1).reflection * (simpleRoot 3 (by decide) 0).reflection) =
    {(simpleRoot 3 (by decide) 0).val, positiveRoot 3 ⟨2, by decide⟩} := by
  ext vector
  constructor
  · intro hvector
    obtain ⟨index, rfl⟩ := selected.positive hvector.1
    rcases (numbered_inversions index).mp hvector with rfl | rfl
    · left
      rw [simpleRoot_zero, positiveRootEquiv_val]
      rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · rw [simpleRoot_zero, positiveRootEquiv_val]
      exact (numbered_inversions _).mpr (Or.inl rfl)
    · exact (numbered_inversions _).mpr (Or.inr rfl)

end Triangle
end Schubert.DihedralSplines
