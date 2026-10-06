import Schubert.FiniteGroupCharacters.FixedRepresentation
import Schubert.DihedralSplines.LowLeftAction
import Schubert.DihedralSplines.QuotientRepresentation

/-! # Full and low-degree fixed quotient representations -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The full left degree action is trivial on the exact canonical length fiber. -/
theorem full_piece_iso (degree : ℕ) :
    Nonempty (RootSubset.Left.pieceFDRep (RootSubset.full n) hthree degree ≅
      ⨁ fun _ : Fin (Nat.card {vertex : DihedralGroup n // length n hthree vertex = degree}) =>
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  let := RootSubset.Left.quotient_finite (RootSubset.full n) hthree
  have hdimension := FlowupSpline.Left.piece_finrank (HessenbergIdeal.full n hthree) degree
  change Module.finrank ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) =
    Nat.card {vertex : DihedralGroup n // (RootSubset.full n).length vertex = degree} at hdimension
  simp_rw [RootSubset.length_full n hthree] at hdimension
  have hiso := fixed_iso (RootSubset.Left.pieceRepresentation (RootSubset.full n) hthree degree)
    (RootSubset.Left.full_piece_fixed n hthree degree)
  rw [hdimension] at hiso
  exact hiso

/-- The injected full left quotient image has its inherited finite group action. -/
def fullImageFDRep (degree : ℕ) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let : AddCommGroup (RootSubset.Left.piece (RootSubset.full n) hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (fullPieceIntertwiner ideal degree).range.toSubmodule :=
    Submodule.addCommGroup _
  let : Module ℂ (fullPieceIntertwiner ideal degree).range.toSubmodule := Submodule.module _
  exact FDRep.of (fullPieceIntertwiner ideal degree).range.toRepresentation

/-- The full quotient image consists of one fixed vector at zero and two thereafter. -/
theorem full_image_iso (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree ≤ half) :
    Nonempty (fullImageFDRep ideal degree ≅
      ⨁ fun _ : Fin (if degree = 0 then 1 else 2) =>
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let : AddCommGroup (RootSubset.Left.piece (RootSubset.full n) hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  have hfixed : ∀ element value,
      (fullPieceIntertwiner ideal degree).range.toRepresentation element value = value := by
    intro element value
    apply Subtype.ext
    obtain ⟨original, horiginal⟩ := value.property
    change RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree element
      value.val = value.val
    rw [← horiginal]
    exact fullPieceMap_fixed ideal degree element original
  let : AddCommGroup (fullPieceIntertwiner ideal degree).range.toSubmodule :=
    Submodule.addCommGroup _
  let : Module ℂ (fullPieceIntertwiner ideal degree).range.toSubmodule := Submodule.module _
  have hiso := fixed_iso (fullPieceIntertwiner ideal degree).range.toRepresentation hfixed
  have hdimension := fullPieceMap_range_finrank ideal half hhalf hproper degree hdegree
  change Module.finrank ℂ (fullPieceIntertwiner ideal degree).range.toSubmodule =
    (if degree = 0 then 1 else 2) at hdimension
  rw [hdimension] at hiso
  exact hiso

/-- Every left quotient degree below the half threshold is the exact fixed sum. -/
theorem low_piece_iso (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) (hdegree : degree < half) :
    Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree ≅
      ⨁ fun _ : Fin (if degree = 0 then 1 else 2) =>
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let : AddCommGroup (RootSubset.Left.piece (RootSubset.full n) hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece (RootSubset.full n) hthree degree) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  have hdimension := fullPieceMap_range_finrank ideal half hhalf hproper degree hdegree.le
  rw [LinearMap.range_eq_top.mpr (fullPieceMap_bijective ideal half hhalf degree hdegree).2,
    finrank_top] at hdimension
  have hiso := fixed_iso (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree)
    (low_piece_fixed ideal half hhalf degree hdegree)
  rw [hdimension] at hiso
  exact hiso

end Schubert.DihedralSplines.HessenbergIdeal.Left
