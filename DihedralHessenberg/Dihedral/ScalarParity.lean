import DihedralHessenberg.Dihedral.ScalarCharacters

/-! # Coordinate parity of the even scalar characters -/

noncomputable section

namespace Schubert.Dihedral

/-- Reduction modulo two computes the parity of the canonical rotation coordinate. -/
theorem reduction_two_val (n : ℕ) [NeZero n] (heven : Even n) (coordinate : ZMod n) :
    (ZMod.castHom (even_iff_two_dvd.mp heven) (ZMod 2) coordinate).val =
      coordinate.val % 2 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val coordinate]
  rw [map_natCast, ZMod.val_natCast]

/-- The even scalar character evaluates rotations by coordinate parity. -/
theorem evenScalarCharacter_r (n : ℕ) [NeZero n] (heven : Even n)
    (reflectionNegative : Bool) (coordinate : ZMod n) :
    evenScalarCharacter n heven reflectionNegative (.r coordinate) =
      (-1 : ℂ) ^ (coordinate.val % 2) := by
  change (-1 : ℂ) ^
    (ZMod.castHom (even_iff_two_dvd.mp heven) (ZMod 2) coordinate).val = _
  rw [reduction_two_val n heven coordinate]

/-- The even scalar character evaluates reflections by sign and coordinate parity. -/
theorem evenScalarCharacter_sr (n : ℕ) [NeZero n] (heven : Even n)
    (reflectionNegative : Bool) (coordinate : ZMod n) :
    evenScalarCharacter n heven reflectionNegative (.sr coordinate) =
      (if reflectionNegative then -1 else 1) * (-1 : ℂ) ^ (coordinate.val % 2) := by
  change (if reflectionNegative then -1 else 1) * (-1 : ℂ) ^
    (ZMod.castHom (even_iff_two_dvd.mp heven) (ZMod 2) coordinate).val = _
  rw [reduction_two_val n heven coordinate]

end Schubert.Dihedral
