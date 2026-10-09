import DihedralHessenberg.Dihedral.ScalarCharacters
import DihedralHessenberg.Dihedral.AlternatingWords
import TauCeti.RepresentationTheory.Simple.Basic

/-! # Dimensions, simplicity and length parity of scalar dihedral representations -/

noncomputable section

open Schubert.FiniteGroupCharacters

namespace Schubert.Dihedral

/-- The determinant sign equals the parity of the canonical Coxeter length. -/
theorem signCharacter_length (n : ℕ) (hthree : 3 ≤ n) [NeZero n]
    (element : DihedralGroup n) : signCharacter n element = (-1 : ℂ) ^ length n hthree element := by
  cases element with
  | r coordinate =>
      rw [signCharacter_r, length_r]
      simp [pow_mul]
  | sr coordinate =>
      rw [signCharacter_sr, length_sr]
      by_cases hzero : coordinate = 0
      · simp [hzero]
      · simp only [hzero, ↓reduceIte]
        have hpos : 0 < coordinate.val := by
          by_contra h
          have hval : coordinate.val = 0 := by omega
          exact hzero (by rw [← ZMod.natCast_zmod_val coordinate, hval, Nat.cast_zero])
        rw [min_def]
        split_ifs
        · rw [show 2 * coordinate.val - 1 = 2 * (coordinate.val - 1) + 1 by omega]
          simp [pow_add, pow_mul]
        · simp [pow_add, pow_mul]

/-- The sign object has complex dimension one. -/
theorem signFDRep_finrank (n : ℕ) [NeZero n] : Module.finrank ℂ (signFDRep n) = 1 := by
  change Module.finrank ℂ ℂ = 1
  simp

/-- Each even scalar object has complex dimension one. -/
theorem evenScalarFDRep_finrank (n : ℕ) (heven : Even n) (negative : Bool) :
    Module.finrank ℂ (evenScalarFDRep n heven negative) = 1 := by
  change Module.finrank ℂ ℂ = 1
  simp

/-- The sign object is simple in the standard representation category. -/
theorem signFDRep_simple (n : ℕ) [NeZero n] : CategoryTheory.Simple (signFDRep n) := by
  apply (FDRep.simple_iff_isIrreducible _).mpr
  exact ScalarCharacter.irreducible (signCharacter n)

/-- Each even scalar object is simple in the standard representation category. -/
theorem evenScalarFDRep_simple (n : ℕ) (heven : Even n) (negative : Bool) :
    CategoryTheory.Simple (evenScalarFDRep n heven negative) := by
  apply (FDRep.simple_iff_isIrreducible _).mpr
  exact ScalarCharacter.irreducible (evenScalarCharacter n heven negative)

end Schubert.Dihedral
