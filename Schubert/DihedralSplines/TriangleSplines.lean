import Schubert.DihedralSplines.DiagramTable
import Schubert.Dihedral.A2Roots

/-! # Polynomial values in the triangle spline illustrations -/

noncomputable section
namespace Schubert.DihedralSplines.TriangleIllustrations
open Schubert.Dihedral

private abbrev firstForm := (simpleRoot 3 (by decide) 0).form
private abbrev secondForm := (simpleRoot 3 (by decide) 1).form
private abbrev thirdForm := (positiveRootEquiv 3 ⟨2, by decide⟩).form

private theorem third_eq : thirdForm = firstForm + secondForm := by
  have h : positiveRoot 3 ⟨2, by decide⟩ =
      positiveRoot 3 ⟨0, by decide⟩ + positiveRoot 3 ⟨1, by decide⟩ := by
    simp only [RootLattice.a2_numbered]
    rfl
  have hp := congrArg (fun vector => linearPolynomial (complexify vector)) h
  convert hp using 1 <;> simp [thirdForm, firstForm, secondForm, PositiveRoot.form, simpleRoot_zero,
    simpleRoot_one, positiveRootEquiv_val, firstSimpleRootIndex, secondSimpleRootIndex,
    linearPolynomial, complexify, map_add]
  all_goals ring

/-- The six displayed functions retain the triangle word vertices and root forms. -/
def value (diagram : Fin 6) (vertex : DihedralGroup 3) : CoordinatePolynomial :=
  let a := firstForm
  let b := secondForm
  let c := firstForm + secondForm
  match vertex with
  | .r coordinate =>
    (![![1, 1, 1], ![0, c, b], ![0, a, c], ![0, a * c, 0],
      ![0, 0, b * c], ![0, 0, 0]] diagram) ⟨coordinate.val, coordinate.val_lt⟩
  | .sr coordinate =>
    (![![1, 1, 1], ![0, b, c], ![a, 0, c], ![0, 0, a * c],
      ![0, 0, b * c], ![0, 0, a * b * c]] diagram) ⟨coordinate.val, coordinate.val_lt⟩

private theorem pairs_eq : Triangle.pairs =
    let first := (simpleRoot 3 (by decide) 0).reflection
    let second := (simpleRoot 3 (by decide) 1).reflection
    ![(1, second), (1, first), (second, second * first), (first, first * second),
      (first * second, first * second * first),
      (second * first, first * second * first), (1, first * second * first),
      (first * second, second), (second * first, first)] := rfl

private theorem labels_eq (row : Fin 9) :
    linearPolynomial (complexify (Triangle.labels row)) =
      ![secondForm, firstForm, thirdForm, thirdForm, secondForm, firstForm,
        thirdForm, -firstForm, -secondForm] row := by
  fin_cases row
  all_goals simp [Triangle.labels, firstForm, secondForm, thirdForm, PositiveRoot.form,
    positiveRootEquiv_val, linearPolynomial, complexify]
  all_goals ring

/-- All six word-value rows are precisely the displayed polynomial assignments. -/
theorem word_values (diagram : Fin 6) :
    let first := (simpleRoot 3 (by decide) 0).reflection
    let second := (simpleRoot 3 (by decide) 1).reflection
    let a := (simpleRoot 3 (by decide) 0).form
    let b := (simpleRoot 3 (by decide) 1).form
    let c := (positiveRootEquiv 3 ⟨2, by decide⟩).form
    ![value diagram 1, value diagram second, value diagram first,
      value diagram (first * second), value diagram (second * first),
      value diagram (first * second * first)] =
      (![![1, 1, 1, 1, 1, 1], ![0, b, 0, c, b, c], ![0, 0, a, a, c, c],
        ![0, 0, 0, a * c, 0, a * c], ![0, 0, 0, 0, b * c, b * c],
        ![0, 0, 0, 0, 0, a * b * c]] diagram) := by
  simp only [third_eq]
  fin_cases diagram
  all_goals simp only [simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.one_def]
  all_goals simp only [value]
  all_goals norm_num [ simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
    DihedralGroup.one_def, ZMod.val_zero, ZMod.val_one_eq_one_mod,
    ZMod.val_natCast, ZMod.val_neg_one, ZMod.val_ofNat, thirdForm, -DihedralGroup.r_zero,
    -PositiveRoot.form_equiv]

/-- Every displayed assignment satisfies every triangle edge label. -/
theorem rows (diagram : Fin 6) (row : Fin 9) :
    linearPolynomial (complexify (Triangle.labels row)) ∣
      value diagram (Triangle.pairs row).1 - value diagram (Triangle.pairs row).2 := by
  rw [pairs_eq, labels_eq]
  simp only [third_eq]
  fin_cases diagram <;> fin_cases row
  all_goals simp only [simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.one_def]
  all_goals simp only [value]
  all_goals norm_num [ simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
    DihedralGroup.one_def, ZMod.val_zero, ZMod.val_one_eq_one_mod,
    ZMod.val_natCast, ZMod.val_neg_one, ZMod.val_ofNat, thirdForm, -DihedralGroup.r_zero,
    -PositiveRoot.form_equiv]
  all_goals first
    | exact dvd_zero _
    | (refine ⟨1, ?_⟩; ring; done)
    | (refine ⟨-1, ?_⟩; ring; done)
    | (refine ⟨firstForm, ?_⟩; ring; done)
    | (refine ⟨-firstForm, ?_⟩; ring; done)
    | (refine ⟨secondForm, ?_⟩; ring; done)
    | (refine ⟨-secondForm, ?_⟩; ring; done)
    | (refine ⟨firstForm + secondForm, ?_⟩; ring; done)
    | (refine ⟨-(firstForm + secondForm), ?_⟩; ring; done)
    | (refine ⟨firstForm * secondForm, ?_⟩; ring; done)
    | (refine ⟨-firstForm * secondForm, ?_⟩; ring; done)
    | (refine ⟨firstForm * (firstForm + secondForm), ?_⟩; ring; done)
    | (refine ⟨secondForm * (firstForm + secondForm), ?_⟩; ring)

/-- All six triangle diagrams are splines on the full positive-root graph. -/
theorem isSpline (diagram : Fin 6) : Triangle.selected.IsSpline (value diagram) :=
  (Triangle.selected.isSpline_iff_table (by decide) Triangle.pairs Triangle.edge_mem
    (fun row => linearPolynomial (complexify (Triangle.labels row))) Triangle.edge_labels
    Triangle.edges (value diagram)).mpr (rows diagram)

end Schubert.DihedralSplines.TriangleIllustrations
