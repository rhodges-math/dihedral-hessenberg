import DihedralHessenberg.Paper.QuotientRepresentation
import DihedralHessenberg.Paper.FlowupBasis
import DihedralHessenberg.Paper.HessenbergMiddle

/-! # Exact dimensions of the middle quotient degrees -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Even middle dimensions count the homogeneous flow-up quotient basis. -/
theorem middle_dimension_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half) :
    Module.finrank ℂ (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) =
      2 * n - 4 * half + 2 := by
  classical
  change Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree half) = _
  rw [FlowupSpline.Left.piece_finrank ideal half, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp_rw [ideal.length_indexed]
  exact ideal.indexed.card_length_eq_middle_of_even half (by rwa [← ideal.ncard_indexed])

/-- Odd middle dimensions count the homogeneous flow-up quotient basis. -/
theorem middle_dimension_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1) :
    Module.finrank ℂ (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) =
      n - 2 * half + 1 := by
  classical
  change Module.finrank ℂ (RootSubset.Left.piece ideal.toRootSubset hthree half) = _
  rw [FlowupSpline.Left.piece_finrank ideal half, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp_rw [ideal.length_indexed]
  exact (ideal.indexed.card_length_eq_middle_of_odd half
    (by rwa [← ideal.ncard_indexed])).1
end Left

namespace Right
/-- Even middle dimensions count the homogeneous flow-up quotient basis. -/
theorem middle_dimension_even (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half) :
    Module.finrank ℂ (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
      2 * n - 4 * half + 2 := by
  classical
  change Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree half) = _
  rw [FlowupSpline.Right.piece_finrank ideal half, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp_rw [ideal.length_indexed]
  exact ideal.indexed.card_length_eq_middle_of_even half (by rwa [← ideal.ncard_indexed])

/-- Odd middle dimensions count the homogeneous flow-up quotient basis. -/
theorem middle_dimension_odd (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half + 1) :
    Module.finrank ℂ (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) =
      n - 2 * half + 1 := by
  classical
  change Module.finrank ℂ (RootSubset.Right.piece ideal.toRootSubset hthree half) = _
  rw [FlowupSpline.Right.piece_finrank ideal half, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  simp_rw [ideal.length_indexed]
  exact (ideal.indexed.card_length_eq_middle_of_odd half
    (by rwa [← ideal.ncard_indexed])).1
end Right

end Schubert.DihedralSplines.HessenbergIdeal
