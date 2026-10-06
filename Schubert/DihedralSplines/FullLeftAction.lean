import Schubert.DihedralSplines.BorelAction
import Schubert.DihedralSplines.PaperQuotientAction
import Schubert.Dihedral.InvariantsBasic
import Schubert.Splines.QuotientFinite

/-! # The dot action on the full left coordinate quotient -/

noncomputable section
namespace Schubert.Dihedral.RootSubset.Left
open Schubert.Dihedral Schubert.DihedralSplines
open scoped TensorProduct

/-- Constant-coordinate classes evaluate the polynomial constant coefficient. -/
theorem constant_map {n : ℕ} (selected : RootSubset n) (hthree : 3 ≤ n)
    (polynomial : CoordinatePolynomial) :
    quotientMap selected hthree (selected.constantHom hthree polynomial) =
      algebraMap ℂ (Quotient selected hthree) polynomial.constantCoeff := by
  let map : CoordinatePolynomial →ₐ[ℂ] Quotient selected hthree :=
    (quotientMap selected hthree).comp (selected.constantHom hthree)
  have hzero (coordinate : Fin 2) : map (MvPolynomial.X coordinate) = 0 :=
    coordinate_zero selected hthree coordinate
  exact Schubert.Splines.QuotientFinite.apply_eq_constantCoeff
    (K := ℂ) (P := Fin 2) (A := Quotient selected hthree) map hzero polynomial

/-- Every class in the full left quotient is fixed by the dot action. -/
theorem full_dot_fixed (n : ℕ) [NeZero n] (hthree : 3 ≤ n)
    (element : DihedralGroup n) (value : Quotient (RootSubset.full n) hthree) :
    dotEquiv (RootSubset.full n) hthree element value = value := by
  let := (RootSubset.full n).leftAlgebra hthree
  obtain ⟨representative, rfl⟩ := map_surjective (RootSubset.full n) hthree value
  obtain ⟨tensor, rfl⟩ := (borelEquiv n hthree).surjective representative
  rw [dot_map]
  induction tensor using TensorProduct.inductionOn with
  | tmul first second =>
    rw [borelEquiv_dot_tmul]
    have ht (polynomial : CoordinatePolynomial) :
        borelEquiv n hthree (polynomial ⊗ₜ[invariantSubalgebra n] second) =
          (RootSubset.full n).constantHom hthree polynomial *
            (RootSubset.full n).orbitHom hthree second := by
      apply Subtype.ext
      funext current
      rw [borelEquiv_tmul]
      rfl
    rw [ht, ht, map_mul, map_mul, constant_map, constant_map,
      polynomialAction_constantCoeff]
  | add first second hfirst hsecond =>
    change quotientMap (RootSubset.full n) hthree
      ((RootSubset.full n).dotEquiv hthree element (borelEquiv n hthree (first + second))) = _
    simp only [map_add]
    change quotientMap (RootSubset.full n) hthree
        ((RootSubset.full n).dot hthree element (borelEquiv n hthree first)) +
      quotientMap (RootSubset.full n) hthree
        ((RootSubset.full n).dot hthree element (borelEquiv n hthree second)) = _
    rw [hfirst, hsecond]

/-- Each full left quotient degree has the trivial action. -/
theorem full_piece_fixed (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (degree : ℕ)
    (element : DihedralGroup n) (value : piece (RootSubset.full n) hthree degree) :
    pieceRepresentation (RootSubset.full n) hthree degree element value = value := by
  apply Subtype.ext
  exact full_dot_fixed n hthree element value.val
end Schubert.Dihedral.RootSubset.Left
