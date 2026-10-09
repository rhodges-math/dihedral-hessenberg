import DihedralHessenberg.Dihedral.SignTwist

/-! # Scalar tensor products with dihedral sign -/

noncomputable section

open CategoryTheory MonoidalCategory

namespace Schubert.Dihedral

/-- The tensor square of determinant sign is the trivial representation. -/
theorem sign_square_iso (n : ℕ) [NeZero n] :
    Nonempty ((signFDRep n ⊗ signFDRep n) ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_tensor, Pi.mul_apply, FDRep.character_of_trivial, signFDRep_character]
  cases element with
  | r coordinate => rw [signCharacter_r]; norm_num
  | sr coordinate => rw [signCharacter_sr]; norm_num

/-- Sign multiplication squares to the trivial class. -/
theorem sign_square_class (n : ℕ) [NeZero n] :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      TauCeti.SplitK0.of (signFDRep n) =
        TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  rw [TauCeti.SplitK0.of_mul_of]
  obtain ⟨isomorphism⟩ := sign_square_iso n
  exact TauCeti.SplitK0.of_congr isomorphism

/-- Tensoring sign with the trivial representation leaves sign unchanged. -/
theorem sign_trivial_iso (n : ℕ) [NeZero n] :
    Nonempty ((signFDRep n ⊗ FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) ≅
      signFDRep n) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_tensor, Pi.mul_apply, FDRep.character_of_trivial, mul_one]

/-- The trivial class is the multiplicative unit on the sign class. -/
theorem sign_trivial_class (n : ℕ) [NeZero n] :
    (TauCeti.SplitK0.of (signFDRep n) : TauCeti.repRing ℂ (DihedralGroup n)) *
      TauCeti.SplitK0.of (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) =
        TauCeti.SplitK0.of (signFDRep n) := by
  rw [TauCeti.SplitK0.of_mul_of]
  obtain ⟨isomorphism⟩ := sign_trivial_iso n
  exact TauCeti.SplitK0.of_congr isomorphism

end Schubert.Dihedral
