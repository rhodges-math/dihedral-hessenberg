import Schubert.DihedralSplines.OppositeFlowup
import Schubert.DihedralSplines.GeometricQuotientBasis

/-! # Degree bases and complementary partners in geometric quotients -/

noncomputable section
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.Splines

variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- Original left quotient basis vectors of one Hessenberg degree. -/
def pieceBasis (degree : ℕ) :
    Module.Basis {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}
      ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := by
  letI := ideal.toRootSubset.leftAlgebra hthree
  exact RootSubset.Left.quotientPieceBasis ideal.toRootSubset hthree (basis ideal)
    ideal.toRootSubset.length (fun vertex => by rw [basis_apply]; exact homogeneous ideal vertex)
    degree

/-- Each degree basis vector is its flow-up quotient class. -/
theorem pieceBasis_apply (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    (pieceBasis ideal degree index : RootSubset.Left.Quotient ideal.toRootSubset hthree) =
      RootSubset.Left.quotientMap ideal.toRootSubset hthree (spline ideal index.val) := by
  let := ideal.toRootSubset.leftAlgebra hthree
  let := RootSubset.Left.gradedAlgebra ideal.toRootSubset hthree
  unfold pieceBasis RootSubset.Left.quotientPieceBasis
  rw [homogeneousPieceBasis_apply, RootSubset.Left.quotientBasis_apply, basis_apply]

/-- The downward class paired with a degree-indexed flow-up vector. -/
def oppositeClass (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    RootSubset.Left.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) :=
  ⟨RootSubset.Left.quotientMap ideal.toRootSubset hthree (opposite ideal index.val),
    (RootSubset.Left.mem_piece _ _ _ _).mpr ⟨opposite ideal index.val,
      by simpa only [index.property] using opposite_homogeneous ideal index.val, rfl⟩⟩

/-- A downward piece vector retains its translated flow-up representative. -/
theorem oppositeClass_apply (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    (oppositeClass ideal degree index : RootSubset.Left.Quotient ideal.toRootSubset hthree) =
      RootSubset.Left.quotientMap ideal.toRootSubset hthree (opposite ideal index.val) := rfl

end Left
namespace Right

/-- Original right quotient basis vectors of one Hessenberg degree. -/
def pieceBasis (degree : ℕ) :
    Module.Basis {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}
      ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := by
  letI := ideal.toRootSubset.rightAlgebra hthree
  exact RootSubset.Right.quotientPieceBasis ideal.toRootSubset hthree (basis ideal)
    ideal.toRootSubset.length (fun vertex => by rw [basis_apply]; exact homogeneous ideal vertex)
    degree

/-- Each degree basis vector is its flow-up quotient class. -/
theorem pieceBasis_apply (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    (pieceBasis ideal degree index : RootSubset.Right.Quotient ideal.toRootSubset hthree) =
      RootSubset.Right.quotientMap ideal.toRootSubset hthree (spline ideal index.val) := by
  let := ideal.toRootSubset.rightAlgebra hthree
  let := RootSubset.Right.gradedAlgebra ideal.toRootSubset hthree
  unfold pieceBasis RootSubset.Right.quotientPieceBasis
  rw [homogeneousPieceBasis_apply, RootSubset.Right.quotientBasis_apply, basis_apply]

/-- The downward class paired with a degree-indexed flow-up vector. -/
def oppositeClass (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    RootSubset.Right.piece ideal.toRootSubset hthree (ideal.carrier.ncard - degree) :=
  ⟨RootSubset.Right.quotientMap ideal.toRootSubset hthree (opposite ideal index.val),
    (RootSubset.Right.mem_piece _ _ _ _).mpr ⟨opposite ideal index.val,
      by simpa only [index.property] using opposite_homogeneous ideal index.val, rfl⟩⟩

/-- A downward piece vector retains its translated flow-up representative. -/
theorem oppositeClass_apply (degree : ℕ)
    (index : {vertex : DihedralGroup n // ideal.toRootSubset.length vertex = degree}) :
    (oppositeClass ideal degree index : RootSubset.Right.Quotient ideal.toRootSubset hthree) =
      RootSubset.Right.quotientMap ideal.toRootSubset hthree (opposite ideal index.val) := rfl

end Right
end Schubert.DihedralSplines.FlowupSpline
