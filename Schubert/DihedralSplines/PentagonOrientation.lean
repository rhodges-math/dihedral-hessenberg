import Schubert.DihedralSplines.PentagonGraph
import Schubert.DihedralSplines.OrientedGraph
import Schubert.Dihedral.ReflectionIndex
import Schubert.Dihedral.AlternatingWords
import Mathlib.Tactic

/-! # The selected three-root endpoint graph of the pentagon -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem pentagon_edges (selected : RootSubset 5)
    (hcarrier : selected.carrier =
      {(positiveRootEquiv 5 ⟨0, by decide⟩).val,
        (positiveRootEquiv 5 ⟨1, by decide⟩).val,
        (positiveRootEquiv 5 ⟨2, by decide⟩).val})
    (source target : DihedralGroup 5) :
    (source, target) ∈ selected.edges ↔
      target = source * DihedralGroup.sr 0 ∨
      target = source * DihedralGroup.sr 1 ∨
      target = source * DihedralGroup.sr 4 := by
  have hmem (alpha : PositiveRoot 5) : alpha.val ∈ selected ↔
      alpha = positiveRootEquiv 5 ⟨0, by decide⟩ ∨
      alpha = positiveRootEquiv 5 ⟨1, by decide⟩ ∨
      alpha = positiveRootEquiv 5 ⟨2, by decide⟩ := by
    change alpha.val ∈ selected.carrier ↔ _
    rw [hcarrier]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
  rw [RootSubset.mem_edges]
  simp only [hmem, or_and_right, exists_or, exists_eq_left]
  have hnormal (index : PositiveRootIndex 5) :
      (positiveRootEquiv 5 index).reflection = DihedralGroup.sr (reflectionCoordinate index) := by
    rw [PositiveRoot.reflection_equiv, rootReflection_eq_sr]
  simp only [hnormal]
  norm_num [reflectionCoordinate]
  rfl

set_option maxHeartbeats 2000000 in
/-- The length orientation of the three-root pentagon graph has the fifteen stated word edges. -/
theorem pentagon_oriented (selected : RootSubset 5)
    (hcarrier : selected.carrier =
      {(positiveRootEquiv 5 ⟨0, by decide⟩).val,
        (positiveRootEquiv 5 ⟨1, by decide⟩).val,
        (positiveRootEquiv 5 ⟨2, by decide⟩).val}) :
    let a := (simpleRoot 5 (by decide) 0).reflection
    let b := (simpleRoot 5 (by decide) 1).reflection
    selected.orientedEdges (by decide) =
      {(1, a), (1, b), (1, a * b * a), (a, a * b), (a, b * a),
        (a * b, a * b * a), (a * b, a * b * a * b * a),
        (a * b * a, a * b * a * b), (a * b * a * b, a * b * a * b * a),
        (b * a * b * a, a * b * a * b * a),
        (b * a * b, b * a * b * a), (b * a * b, a * b * a * b),
        (b * a, b * a * b), (b, b * a), (b, b * a * b * a)} := by
  dsimp only
  ext ⟨source, target⟩
  change ((source, target) ∈ selected.edges ∧
    length 5 (by decide) source < length 5 (by decide) target) ↔ _
  rw [pentagon_edges selected hcarrier]
  simp only [simpleRoot_reflection, simpleReflection_zero, simpleReflection_one,
    firstSimpleReflection, secondSimpleReflection]
  simp only [DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr]
  have henum (coordinate : ZMod 5) :
      ∃ index : Fin 5, coordinate = (index.val : ZMod 5) := by
    exact ⟨⟨coordinate.val, coordinate.val_lt⟩, (ZMod.natCast_zmod_val coordinate).symm⟩
  cases source with
  | r first =>
    obtain ⟨first, rfl⟩ := henum first
    cases target with
    | r second =>
      obtain ⟨second, rfl⟩ := henum second
      fin_cases first <;> fin_cases second <;>
        simp [-DihedralGroup.r_zero, DihedralGroup.one_def, length_r]
    | sr second =>
      obtain ⟨second, rfl⟩ := henum second
      fin_cases first <;> fin_cases second <;>
        simp [-DihedralGroup.r_zero, DihedralGroup.one_def, length_r, length_sr]
      all_goals decide
  | sr first =>
    obtain ⟨first, rfl⟩ := henum first
    cases target with
    | r second =>
      obtain ⟨second, rfl⟩ := henum second
      fin_cases first <;> fin_cases second <;>
        simp [-DihedralGroup.r_zero, DihedralGroup.one_def, length_r, length_sr]
      all_goals decide
    | sr second =>
      obtain ⟨second, rfl⟩ := henum second
      fin_cases first <;> fin_cases second <;>
        simp [-DihedralGroup.r_zero, DihedralGroup.one_def, length_sr]

end Schubert.DihedralSplines
