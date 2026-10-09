import DihedralHessenberg.Paper.DiagramTable

/-! # Polynomial values in the square spline illustrations -/

noncomputable section
namespace Schubert.DihedralSplines.SquareIllustrations
open Schubert.Dihedral

/-- The three displayed functions, with the rotation and reflection vertices. -/
def value (diagram : Fin 3) (vertex : DihedralGroup 4) : CoordinatePolynomial :=
  let x := MvPolynomial.X (0 : Fin 2)
  let y := MvPolynomial.X (1 : Fin 2)
  match vertex with
  | .r coordinate =>
    (![![1, 1, 1, 1], ![0, -y, 0, x + y], ![0, -x - y, 0, -y]] diagram)
      ⟨coordinate.val, coordinate.val_lt⟩
  | .sr coordinate =>
    (![![1, 1, 1, 1], ![x, x - y, 0, 0], ![0, 0, x, -x + y]] diagram)
      ⟨coordinate.val, coordinate.val_lt⟩

/-- The evaluations at the eight word vertices are exactly the displayed values. -/
theorem word_values (diagram : Fin 3) :
    let first := (simpleRoot 4 (by decide) 0).reflection
    let second := (simpleRoot 4 (by decide) 1).reflection
    let x := MvPolynomial.X (0 : Fin 2)
    let y := MvPolynomial.X (1 : Fin 2)
    ![value diagram 1, value diagram second, value diagram first,
      value diagram (first * second), value diagram (second * first),
      value diagram (second * first * second), value diagram (first * second * first),
      value diagram (first * second * first * second)] =
      (![![1, 1, 1, 1, 1, 1, 1, 1], ![0, x - y, x, -y, x + y, 0, 0, 0],
        ![0, 0, 0, -x - y, -y, x, -x + y, 0]] diagram) := by
  fin_cases diagram
  all_goals simp only [simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.one_def]
  all_goals simp only [value]
  all_goals norm_num [ simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.sr_mul_sr,
    DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_r,
    DihedralGroup.one_def, ZMod.val_zero, ZMod.val_one_eq_one_mod,
    ZMod.val_natCast, ZMod.val_neg_one, ZMod.val_ofNat, -DihedralGroup.r_zero,
    -PositiveRoot.form_equiv]

private theorem pairs_eq : Square.pairs =
    let first := (simpleRoot 4 (by decide) 0).reflection
    let second := (simpleRoot 4 (by decide) 1).reflection
    ![(1, second), (1, first), (second, second * first), (first, first * second),
      (first * second, first * second * first),
      (second * first, second * first * second),
      (second * first * second, first * second * first * second),
      (first * second * first, first * second * first * second)] := rfl

/-- Every displayed function satisfies every exact square edge generator. -/
theorem rows (diagram : Fin 3) (row : Fin 8) :
    Square.labels row ∣ value diagram (Square.pairs row).1 -
      value diagram (Square.pairs row).2 := by
  rw [pairs_eq]
  fin_cases diagram <;> fin_cases row
  all_goals simp only [simpleRoot_reflection, simpleReflection,
    firstSimpleReflection, secondSimpleReflection, DihedralGroup.one_def]
  all_goals simp only [value]
  all_goals norm_num [ Square.labels, simpleRoot_reflection,
    simpleReflection, firstSimpleReflection, secondSimpleReflection,
    DihedralGroup.sr_mul_sr, DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r,
    DihedralGroup.r_mul_r, DihedralGroup.one_def, ZMod.val_zero,
    ZMod.val_one_eq_one_mod, ZMod.val_natCast, ZMod.val_neg_one, ZMod.val_ofNat,
    -DihedralGroup.r_zero,
    -PositiveRoot.form_equiv]
  all_goals first
    | exact dvd_zero _
    | (refine ⟨1, ?_⟩; ring; done)
    | (refine ⟨-1, ?_⟩; ring; done)
    | (refine ⟨2, ?_⟩; ring; done)
    | (refine ⟨-2, ?_⟩; ring)

/-- The three square value assignments are splines on the selected graph. -/
theorem isSpline (diagram : Fin 3) : Square.selected.IsSpline (value diagram) :=
  (Square.selected.isSpline_iff_table (by decide) Square.pairs Square.edge_mem Square.labels
    Square.edge_labels Square.edges (value diagram)).mpr (rows diagram)

end Schubert.DihedralSplines.SquareIllustrations
