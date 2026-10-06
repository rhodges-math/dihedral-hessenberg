import Schubert.DihedralSplines.FullLeftClass
import Schubert.DihedralSplines.FullRightDeterminant

/-! # Equal full quotient degree spaces with distinct actions -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.SchubertSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable (n : ℕ) [NeZero n] (hthree : 3 ≤ n)

/-- The two full quotient degree spaces have the same dimension. -/
theorem full_piece_finrank_eq (degree : ℕ) :
    Module.finrank ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) =
      Module.finrank ℂ (RootSubset.Right.piece (RootSubset.full n) hthree degree) := by
  have hl := FlowupSpline.Left.piece_finrank (HessenbergIdeal.full n hthree) degree
  have hr := FlowupSpline.Right.piece_finrank (HessenbergIdeal.full n hthree) degree
  exact hl.trans hr.symm

/-- The full quotient degrees have equal underlying graded vector-space types. -/
theorem full_piece_linearEquiv (degree : ℕ) :
    Nonempty (RootSubset.Left.piece (RootSubset.full n) hthree degree ≃ₗ[ℂ]
      RootSubset.Right.piece (RootSubset.full n) hthree degree) := by
  let := RootSubset.Left.quotient_finite (RootSubset.full n) hthree
  let := RootSubset.Right.quotient_finite (RootSubset.full n) hthree
  exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (full_piece_finrank_eq n hthree degree)

/-- The two degree-one actions are not isomorphic as representations. -/
theorem full_piece_not_iso :
    ¬Nonempty (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree 1 ≅
      RootSubset.Right.pieceFDRep (RootSubset.full n) hthree 1) := by
  classical
  have hcard : Nat.card {vertex : DihedralGroup n // length n hthree vertex = 1} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact card_length_eq_of_positive_lt 1 (by omega) (by omega)
  have hleft : (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree 1).character
      (firstSimpleReflection n) = 2 := by
    have h := congrFun (FDRep.char_iso
      (HessenbergIdeal.Left.full_piece_iso (n := n) (hthree := hthree) 1).some)
      (firstSimpleReflection n)
    rw [finiteSum_character] at h
    simpa [← Nat.card_eq_fintype_card, hcard, Nat.card_fin] using h
  have hright : (RootSubset.Right.pieceFDRep (RootSubset.full n) hthree 1).character
      (firstSimpleReflection n) = 0 := by
    rw [RootSubset.Right.pieceFDRep_character, right_character_degree,
      ← coinvariantPieceFDRep_character]
    exact Coinvariant.Middle.character_sr n hthree 1 (by omega) (by omega) 0
  rintro ⟨isomorphism⟩
  have h := congrFun (FDRep.char_iso isomorphism) (firstSimpleReflection n)
  rw [hleft, hright] at h
  norm_num at h

end Schubert.DihedralSplines.SchubertSpline
