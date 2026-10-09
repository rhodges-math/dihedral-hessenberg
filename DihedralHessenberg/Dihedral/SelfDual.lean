import DihedralHessenberg.Dihedral.Conjugacy
import Mathlib.Analysis.Complex.Basic
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # Self-duality of complex dihedral representations -/

noncomputable section

namespace Schubert.Dihedral

/-- The trace character of a dihedral representation is unchanged by group inversion. -/
theorem character_inv {n : ℕ} (object : FDRep ℂ (DihedralGroup n))
    (element : DihedralGroup n) : object.character element⁻¹ = object.character element := by
  cases element with
  | r coordinate =>
      simpa using object.char_conj (.r coordinate) (.sr 0)
  | sr coordinate => rw [DihedralGroup.inv_sr]

/-- Every finite-dimensional complex dihedral representation is isomorphic to its dual. -/
theorem self_dual {n : ℕ} [NeZero n] (object : FDRep ℂ (DihedralGroup n)) :
    Nonempty (object ≅ FDRep.of (Representation.dual object.ρ)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_dual, character_inv]

end Schubert.Dihedral
