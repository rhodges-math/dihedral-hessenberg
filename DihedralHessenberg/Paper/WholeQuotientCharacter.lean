import DihedralHessenberg.FiniteGroupCharacters.HomogeneousCharacter
import DihedralHessenberg.Paper.FlowupPieceBases
import DihedralHessenberg.Paper.QuotientRepresentation
import DihedralHessenberg.FiniteGroupCharacters.FiniteSum

/-! # Whole quotient characters from homogeneous pieces -/

noncomputable section
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The whole quotient action is the sum of its degree characters. -/
theorem whole_character (element : DihedralGroup n) :
    letI := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
    (RootSubset.Left.representation ideal.toRootSubset hthree).character element =
      ∑ degree ∈ Finset.range (ideal.carrier.ncard + 1),
        (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree).character element := by
  classical
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let := RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree
  let action := RootSubset.Left.representation ideal.toRootSubset hthree
  let pieces (degree : ℕ) : Subrepresentation action :=
    { toSubmodule := RootSubset.Left.piece ideal.toRootSubset hthree degree
      apply_mem_toSubmodule := fun g v hv =>
        RootSubset.Left.dot_mem_piece ideal.toRootSubset hthree g degree v hv }
  let basis := RootSubset.Left.quotientBasis ideal.toRootSubset hthree
    (FlowupSpline.Left.basis ideal)
  have hbasis (vertex : DihedralGroup n) :
      basis vertex ∈ (pieces (ideal.toRootSubset.length vertex)).toSubmodule := by
    exact RootSubset.Left.quotientBasis_mem_piece ideal.toRootSubset hthree
      (FlowupSpline.Left.basis ideal) ideal.toRootSubset.length
      (fun w => by
        rw [FlowupSpline.Left.basis_apply]
        exact FlowupSpline.homogeneous ideal w) vertex
  have hbound (vertex : DihedralGroup n) :
      ideal.toRootSubset.length vertex ≤ ideal.carrier.ncard := by
    rw [ideal.length_indexed, ideal.ncard_indexed]
    exact ideal.indexed.length_le_card_roots vertex
  have h := whole_homogeneous_character action pieces basis ideal.toRootSubset.length
    hbasis ideal.carrier.ncard hbound element
  have hpiece (degree : ℕ) : (pieces degree).toRepresentation =
      RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree := by
    ext g value
    rfl
  simp_rw [hpiece] at h
  simpa only [RootSubset.Left.pieceFDRep_character] using h

/-- The standard finite-dimensional object retains the whole quotient action. -/
def wholeFDRep : FDRep ℂ (DihedralGroup n) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  exact FDRep.of (RootSubset.Left.representation ideal.toRootSubset hthree)

/-- Forgetting homogeneous degrees sums precisely the degree classes. -/
theorem whole_class :
    (TauCeti.SplitK0.of (wholeFDRep ideal) : TauCeti.repRing ℂ (DihedralGroup n)) =
      ∑ degree ∈ Finset.range (ideal.carrier.ncard + 1),
        TauCeti.SplitK0.of (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_sum]
  funext element
  simp only [Finset.sum_apply, TauCeti.repRingCharacter_of]
  rw [show (wholeFDRep ideal).character =
    (RootSubset.Left.representation ideal.toRootSubset hthree).character from
      FDRep.character_of _]
  exact whole_character ideal element

end Schubert.DihedralSplines.HessenbergIdeal.Left
