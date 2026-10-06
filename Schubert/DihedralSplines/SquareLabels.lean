import Schubert.Dihedral.ConeCoordinates
import Schubert.Dihedral.SimpleRootObjects
import Schubert.DihedralSplines.PaperGraph

/-! # The second simple root of the square and its edge label -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

/-- The second simple root of the square is `(-√2/2, √2/2)`. -/
theorem square_second_vector :
    (simpleRoot 4 (by decide) 1).val =
      ![-Real.sqrt 2 / 2, Real.sqrt 2 / 2] := by
  rw [simpleRoot_one, positiveRootEquiv_val, secondSimpleRoot_eq_unitRootAt]
  simp only [unitRootAt, Nat.cast_ofNat, Real.cos_pi_sub, Real.sin_pi_sub,
    Real.cos_pi_div_four, Real.sin_pi_div_four, neg_div]

/-- The linear form of the second simple root of the square is `(√2/2)(-x + y)`. -/
theorem square_second_form :
    (simpleRoot 4 (by decide) 1).form =
      MvPolynomial.C ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        (-MvPolynomial.X 0 + MvPolynomial.X 1) := by
  rw [PositiveRoot.form, square_second_vector]
  simp only [linearPolynomial, complexify, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, neg_div, map_neg]
  ring

/-- The edge from the identity to the second simple reflection has label `(√2/2)(-x + y)`. -/
theorem square_edge_label (selected : RootSubset 4)
    (hmem : (simpleRoot 4 (by decide) 1).val ∈ selected) :
    selected.edgeLabel (selected.edge 1 (simpleRoot 4 (by decide) 1) hmem) =
      MvPolynomial.C ((Real.sqrt 2 / 2 : ℝ) : ℂ) *
        (-MvPolynomial.X 0 + MvPolynomial.X 1) := by
  rw [RootSubset.edgeLabel_edge, realAction_one]
  exact square_second_form

end Schubert.DihedralSplines
