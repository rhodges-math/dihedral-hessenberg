import DihedralHessenberg.FiniteGroupCharacters.HomIntertwiner
import DihedralHessenberg.FiniteGroupCharacters.HomSurvival
import DihedralHessenberg.Paper.HessenbergIdealDecomposition
import DihedralHessenberg.Paper.MiddleOrbitRepresentation

/-! # Survival of injected constituents in coordinate quotients -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- Only constituents accounted for in the homogeneous coordinate kernel can disappear. -/
theorem quotient_survival (degree : ℕ) (test injected : FDRep ℂ (DihedralGroup n))
    (embedding : Representation.IntertwiningMap injected.ρ
      (ideal.toRootSubset.splinePieceRepresentation hthree degree))
    (hinjective : Function.Injective embedding) :
    Module.finrank ℂ (test ⟶ injected) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal degree) +
        Module.finrank ℂ
          (test ⟶ RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let : NeZero (Nat.card (DihedralGroup n) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let kernel := (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  rw [hom_intertwiner_finrank, hom_intertwiner_finrank, hom_intertwiner_finrank]
  exact hom_survival_bound test.ρ injected.ρ embedding hinjective
    (RootSubset.Left.pieceProjection ideal.toRootSubset hthree degree) (by
      intro value
      obtain ⟨original, horiginal, hmap⟩ :=
        (RootSubset.Left.mem_piece ideal.toRootSubset hthree degree value.val).1 value.property
      exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩)

/-- Both middle coset actions supply constituents to the quotient. -/
theorem middle_coset_survival (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (test : FDRep ℂ (DihedralGroup n)) :
    Module.finrank ℂ
      (test ⟶ (simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal half) +
        Module.finrank ℂ
          (test ⟶ RootSubset.Left.pieceFDRep ideal.toRootSubset hthree half) := by
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    (FlowupSpline.middle_coset_iso ideal half hcard hproper first second)
  let embedding := (FlowupSpline.middlePieceMap ideal half hcard hproper first second).comp
    equivalence.toIntertwiningMap
  exact quotient_survival ideal half test _ embedding
    ((FlowupSpline.middlePieceMap_injective ideal half hcard hproper first second).comp
      equivalence.toLinearEquiv.injective)

end Left


namespace Right

/-- Only constituents accounted for in the homogeneous coordinate kernel can disappear. -/
theorem quotient_survival (degree : ℕ) (test injected : FDRep ℂ (DihedralGroup n))
    (embedding : Representation.IntertwiningMap injected.ρ
      (ideal.toRootSubset.splinePieceRepresentation hthree degree))
    (hinjective : Function.Injective embedding) :
    Module.finrank ℂ (test ⟶ injected) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal degree) +
        Module.finrank ℂ
          (test ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) := by
  let : AddCommGroup (ideal.toRootSubset.piece degree) := Submodule.addCommGroup _
  let : Module ℂ (ideal.toRootSubset.piece degree) := Submodule.module _
  let := ideal.splinePiece_finite degree
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let : NeZero (Nat.card (DihedralGroup n) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let kernel := (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree).ker
  let : AddCommGroup kernel.toSubmodule := Submodule.addCommGroup _
  let : Module ℂ kernel.toSubmodule := Submodule.module _
  rw [hom_intertwiner_finrank, hom_intertwiner_finrank, hom_intertwiner_finrank]
  exact hom_survival_bound test.ρ injected.ρ embedding hinjective
    (RootSubset.Right.pieceProjection ideal.toRootSubset hthree degree) (by
      intro value
      obtain ⟨original, horiginal, hmap⟩ :=
        (RootSubset.Right.mem_piece ideal.toRootSubset hthree degree value.val).1 value.property
      exact ⟨⟨original, horiginal⟩, Subtype.ext hmap⟩)

/-- Both middle coset actions supply constituents to the quotient. -/
theorem middle_coset_survival (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : MiddleWitness ideal half (simpleRoot n hthree 1) (n - half))
    (test : FDRep ℂ (DihedralGroup n)) :
    Module.finrank ℂ
      (test ⟶ (simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep) ≤
      Module.finrank ℂ (test ⟶ removedFDRep ideal half) +
        Module.finrank ℂ
          (test ⟶ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree half) := by
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp
    (FlowupSpline.middle_coset_iso ideal half hcard hproper first second)
  let embedding := (FlowupSpline.middlePieceMap ideal half hcard hproper first second).comp
    equivalence.toIntertwiningMap
  exact quotient_survival ideal half test _ embedding
    ((FlowupSpline.middlePieceMap_injective ideal half hcard hproper first second).comp
      equivalence.toLinearEquiv.injective)

end Right

end Schubert.DihedralSplines.HessenbergIdeal
