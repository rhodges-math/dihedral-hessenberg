import DihedralHessenberg.Paper.LowDegreeIdealRestriction
import Mathlib.RepresentationTheory.Intertwining

/-! # Low-degree injections of the full spline quotients -/

noncomputable section
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)
namespace Right

/-- Quotient restriction on a homogeneous degree piece. -/
def fullPieceMap (degree : ℕ) :
    RootSubset.Right.piece (RootSubset.full n) hthree degree →ₗ[ℂ]
      RootSubset.Right.piece ideal.toRootSubset hthree degree where
  toFun value := ⟨RootSubset.Right.restrict ideal.toRootSubset (RootSubset.full n)
    hthree ideal.toRootSubset.positive value.val,
    RootSubset.Right.restrict_mem_piece ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive degree value.val value.property⟩
  map_add' first second := Subtype.ext
    ((RootSubset.Right.restrict ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive).map_add first.val second.val)
  map_smul' scalar value := Subtype.ext
    ((RootSubset.Right.restrict ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive).toLinearMap.map_smul scalar value.val)

/-- Full quotient restriction is injective through the half threshold, including its boundary. -/
theorem fullPieceMap_injective (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree ≤ half) :
    Function.Injective (fullPieceMap ideal degree) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro value hvalue
  have hzero := congrArg Subtype.val (LinearMap.mem_ker.mp hvalue)
  change RootSubset.Right.restrict ideal.toRootSubset (RootSubset.full n)
    hthree ideal.toRootSubset.positive value.val = 0 at hzero
  obtain ⟨original, hhomogeneous, horiginal⟩ :=
    (RootSubset.Right.mem_piece (RootSubset.full n) hthree degree value.val).mp value.property
  rw [← horiginal] at hzero
  change RootSubset.Right.quotientMap ideal.toRootSubset hthree
    (ideal.toRootSubset.restrictFull original) = 0 at hzero
  obtain ⟨preimage, hpreimage, heq⟩ := ideal.rightIdeal_preimage half hhalf degree hdegree
    (ideal.toRootSubset.restrictFull original) hhomogeneous
    ((RootSubset.Right.map_zero_iff ideal.toRootSubset hthree _).mp hzero)
  have hsame : preimage = original :=
    ideal.toRootSubset.restrict_injective (RootSubset.full n) ideal.toRootSubset.positive heq
  apply Subtype.ext
  change value.val = 0
  rw [← horiginal]
  exact (RootSubset.Right.map_zero_iff (RootSubset.full n) hthree _).mpr (hsame ▸ hpreimage)

/-- Degreewise restriction intertwines the quotient representations. -/
def fullPieceIntertwiner (degree : ℕ) :
    Representation.IntertwiningMap
      (RootSubset.Right.pieceRepresentation (RootSubset.full n) hthree degree)
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree) where
  toLinearMap := fullPieceMap ideal degree
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact RootSubset.Right.restrict_dot ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive element value.val

omit [NeZero n] in
/-- The intertwiner is precisely the quotient restriction on representatives. -/
theorem fullPieceIntertwiner_apply (degree : ℕ)
    (value : RootSubset.Right.piece (RootSubset.full n) hthree degree) :
    fullPieceIntertwiner ideal degree value = fullPieceMap ideal degree value := rfl
end Right

namespace Left

/-- Quotient restriction on a homogeneous degree piece. -/
def fullPieceMap (degree : ℕ) :
    RootSubset.Left.piece (RootSubset.full n) hthree degree →ₗ[ℂ]
      RootSubset.Left.piece ideal.toRootSubset hthree degree where
  toFun value := ⟨RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
    hthree ideal.toRootSubset.positive value.val,
    RootSubset.Left.restrict_mem_piece ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive degree value.val value.property⟩
  map_add' first second := Subtype.ext
    ((RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive).map_add first.val second.val)
  map_smul' scalar value := Subtype.ext
    ((RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive).toLinearMap.map_smul scalar value.val)

/-- Full quotient restriction is injective through the half threshold, including its boundary. -/
theorem fullPieceMap_injective (half : ℕ) (hhalf : 2 * half ≤ ideal.carrier.ncard)
    (degree : ℕ) (hdegree : degree ≤ half) :
    Function.Injective (fullPieceMap ideal degree) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro value hvalue
  have hzero := congrArg Subtype.val (LinearMap.mem_ker.mp hvalue)
  change RootSubset.Left.restrict ideal.toRootSubset (RootSubset.full n)
    hthree ideal.toRootSubset.positive value.val = 0 at hzero
  obtain ⟨original, hhomogeneous, horiginal⟩ :=
    (RootSubset.Left.mem_piece (RootSubset.full n) hthree degree value.val).mp value.property
  rw [← horiginal] at hzero
  change RootSubset.Left.quotientMap ideal.toRootSubset hthree
    (ideal.toRootSubset.restrictFull original) = 0 at hzero
  obtain ⟨preimage, hpreimage, heq⟩ := ideal.leftIdeal_preimage half hhalf degree hdegree
    (ideal.toRootSubset.restrictFull original) hhomogeneous
    ((RootSubset.Left.map_zero_iff ideal.toRootSubset hthree _).mp hzero)
  have hsame : preimage = original :=
    ideal.toRootSubset.restrict_injective (RootSubset.full n) ideal.toRootSubset.positive heq
  apply Subtype.ext
  change value.val = 0
  rw [← horiginal]
  exact (RootSubset.Left.map_zero_iff (RootSubset.full n) hthree _).mpr (hsame ▸ hpreimage)

/-- Degreewise restriction intertwines the quotient representations. -/
def fullPieceIntertwiner (degree : ℕ) :
    Representation.IntertwiningMap
      (RootSubset.Left.pieceRepresentation (RootSubset.full n) hthree degree)
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree) where
  toLinearMap := fullPieceMap ideal degree
  isIntertwining' element := by
    apply LinearMap.ext
    intro value
    apply Subtype.ext
    exact RootSubset.Left.restrict_dot ideal.toRootSubset (RootSubset.full n)
      hthree ideal.toRootSubset.positive element value.val

omit [NeZero n] in
/-- The intertwiner is precisely the quotient restriction on representatives. -/
theorem fullPieceIntertwiner_apply (degree : ℕ)
    (value : RootSubset.Left.piece (RootSubset.full n) hthree degree) :
    fullPieceIntertwiner ideal degree value = fullPieceMap ideal degree value := rfl
end Left
end Schubert.DihedralSplines.HessenbergIdeal
