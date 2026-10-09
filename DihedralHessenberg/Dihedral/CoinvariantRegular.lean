import DihedralHessenberg.Dihedral.CoinvariantRegularTrace
import TauCeti.RepresentationTheory.Induction.Permutation
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # The coinvariant algebra as the regular representation -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral.Coinvariant

/-- The finite-dimensional object of the whole coinvariant action. -/
def wholeFDRep (n : ℕ) [NeZero n] : FDRep ℂ (DihedralGroup n) := by
  let := coinvariantAlgebra_finite n
  exact FDRep.of (coinvariantRepresentation n)

/-- The regular character is twice n at the identity and zero elsewhere. -/
theorem regular_character (n : ℕ) [NeZero n] (element : DihedralGroup n) :
    (Representation.leftRegular ℂ (DihedralGroup n)).character element =
      if element = 1 then 2 * (n : ℂ) else 0 := by
  classical
  rw [TauCeti.char_ofMulAction]
  by_cases hone : element = 1
  · subst element
    simp [DihedralGroup.card, Nat.cast_mul]
  · have hempty : IsEmpty {x : DihedralGroup n // element • x = x} := by
      constructor
      rintro ⟨x, hx⟩
      exact hone (mul_right_cancel (show element * x = 1 * x by simpa using hx))
    simp [hone]

/-- The whole coinvariant and regular actions have equal characters. -/
theorem character_regular (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    (coinvariantRepresentation n).character =
      (Representation.leftRegular ℂ (DihedralGroup n)).character := by
  funext element
  rw [regular_character]
  cases element with
  | r coordinate =>
      rw [character_r_whole n hthree]
      simp [DihedralGroup.one_def, -DihedralGroup.r_zero]
  | sr coordinate =>
      rw [character_sr_whole n hthree]
      simp [DihedralGroup.one_def, -DihedralGroup.r_zero]

/-- The whole coinvariant action is isomorphic to the regular representation. -/
theorem regular_iso (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Nonempty (wholeFDRep n ≅ FDRep.of (Representation.leftRegular ℂ (DihedralGroup n))) := by
  apply FDRep.nonempty_iso_of_character_eq
  simpa only [wholeFDRep, FDRep.character_of] using character_regular n hthree

end Schubert.Dihedral.Coinvariant
