import DihedralHessenberg.FiniteGroupCharacters.PairingRepresentation
import DihedralHessenberg.Paper.QuotientPairing
import DihedralHessenberg.Paper.QuotientRepresentation

/-! # Complementary quotient actions and their perfect multiplication pairings -/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- Perfect multiplication is an equivalence to the linear-map representation. -/
def pairingActionEquiv (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Representation.Equiv
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree)
      (Representation.linHom
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree))
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard)) := by
  refine Schubert.FiniteGroupCharacters.pairingActionEquiv _ _ _
    (FlowupSpline.Left.pairingEquiv ideal degree hdegree) ?_
  intro element value partner
  apply Subtype.ext
  exact FlowupSpline.Left.pairingEquiv_dot ideal degree hdegree element value partner

/-- Complementary degree representations are dual tensor top objects. -/
theorem complementary_dual_iso (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree ≅
      FDRep.of (Representation.dual
        (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree)).ρ) ⊗
          RootSubset.Left.pieceFDRep ideal.toRootSubset hthree ideal.carrier.ncard) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree
      ideal.carrier.ncard) := Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree
      ideal.carrier.ncard) := Submodule.module _
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree)) := Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree)) := Submodule.module _
  have hfirst : Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree ≅
      FDRep.of (Representation.linHom
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree))
        (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard))) := by
    apply TauCeti.nonempty_fdRepIso_iff.mpr
    exact ⟨pairingActionEquiv ideal degree hdegree⟩
  exact ⟨hfirst.some.trans (FDRep.dualTensorIsoLinHom
    (V := RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree))
    (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree))
    (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree ideal.carrier.ncard)).symm⟩

end Left

namespace Right

/-- Perfect multiplication is an equivalence to the linear-map representation. -/
def pairingActionEquiv (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Representation.Equiv
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree)
      (Representation.linHom
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree))
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard)) := by
  refine Schubert.FiniteGroupCharacters.pairingActionEquiv _ _ _
    (FlowupSpline.Right.pairingEquiv ideal degree hdegree) ?_
  intro element value partner
  apply Subtype.ext
  exact FlowupSpline.Right.pairingEquiv_dot ideal degree hdegree element value partner

/-- Complementary degree representations are dual tensor top objects. -/
theorem complementary_dual_iso (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree ≅
      FDRep.of (Representation.dual
        (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree)).ρ) ⊗
          RootSubset.Right.pieceFDRep ideal.toRootSubset hthree ideal.carrier.ncard) := by
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree
      ideal.carrier.ncard) := Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree
      ideal.carrier.ncard) := Submodule.module _
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree)) := Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree)) := Submodule.module _
  have hfirst : Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree ≅
      FDRep.of (Representation.linHom
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
          (ideal.carrier.ncard - degree))
        (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard))) := by
    apply TauCeti.nonempty_fdRepIso_iff.mpr
    exact ⟨pairingActionEquiv ideal degree hdegree⟩
  exact ⟨hfirst.some.trans (FDRep.dualTensorIsoLinHom
    (V := RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree))
    (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree))
    (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree ideal.carrier.ncard)).symm⟩

end Right

end Schubert.DihedralSplines.HessenbergIdeal
