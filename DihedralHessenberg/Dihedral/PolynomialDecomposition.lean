import DihedralHessenberg.Dihedral.PolynomialReflection
import TauCeti.RepresentationTheory.RepresentationRing.Injective
import DihedralHessenberg.Dihedral.FrequencyDistinction

/-! # Frequency decompositions of homogeneous polynomial representations -/

noncomputable section
open CategoryTheory Limits
open scoped BigOperators
namespace Schubert.Dihedral

/-- Every polynomial degree is a sum of opposite-weight frequency objects. -/
theorem polynomialPiece_frequency_iso (n : ℕ) [NeZero n] (degree : ℕ) :
    Nonempty (polynomialPieceFDRep n degree ≅
      (⨁ fun index : Fin ((degree + 1) / 2) =>
        frequencyFDRep n (degree - 2 * index.val : ℕ)) ⊞
      (⨁ fun _ : Fin (if Even degree then 1 else 0) =>
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ))) := by
  classical
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_biprod, Pi.add_apply, Schubert.FiniteGroupCharacters.finiteSum_character]
  rw [Schubert.FiniteGroupCharacters.finiteSum_character]
  rcases element with coordinate | coordinate
  · rw [polynomialPiece_character_r_pairs]
    simp
  · rw [polynomialPiece_character_sr]
    simp [frequencyFDRep_character, frequencyRepresentation_character_sr]

/-- Even polynomial degrees contain their paired frequencies and one trivial object. -/
theorem polynomialPiece_even_iso (n : ℕ) [NeZero n] (half : ℕ) :
    Nonempty (polynomialPieceFDRep n (2 * half) ≅
      (⨁ fun index : Fin half => frequencyFDRep n (2 * half - 2 * index.val : ℕ)) ⊞
        FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  classical
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [FDRep.char_biprod, Pi.add_apply, Schubert.FiniteGroupCharacters.finiteSum_character]
  have hsize : (2 * half + 1) / 2 = half := by omega
  have heven : Even (2 * half) := ⟨half, by omega⟩
  rcases element with coordinate | coordinate
  · rw [polynomialPiece_character_r_pairs, hsize]
    simp [heven]
  · rw [polynomialPiece_character_sr]
    simp [heven, frequencyFDRep_character, frequencyRepresentation_character_sr]

/-- Odd polynomial degrees consist exactly of their paired frequency objects. -/
theorem polynomialPiece_odd_iso (n : ℕ) [NeZero n] (half : ℕ) :
    Nonempty (polynomialPieceFDRep n (2 * half + 1) ≅
      ⨁ fun index : Fin (half + 1) =>
        frequencyFDRep n (2 * half + 1 - 2 * index.val : ℕ)) := by
  classical
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [Schubert.FiniteGroupCharacters.finiteSum_character]
  have hsize : (2 * half + 1 + 1) / 2 = half + 1 := by omega
  have hodd : ¬Even (2 * half + 1) := by
    intro ⟨witness, hwitness⟩
    omega
  rcases element with coordinate | coordinate
  · rw [polynomialPiece_character_r_pairs, hsize]
    simp [hodd]
  · rw [polynomialPiece_character_sr]
    simp [hodd, frequencyFDRep_character, frequencyRepresentation_character_sr]

/-- Each positive-frequency summand below half the group order is irreducible. -/
theorem polynomialPiece_frequency_simple (n : ℕ) [NeZero n] (degree : ℕ)
    (hdegree : 2 * degree < n) (index : Fin ((degree + 1) / 2)) :
    CategoryTheory.Simple (frequencyFDRep n (degree - 2 * index.val : ℕ)) := by
  apply frequencyFDRep_simple_of_lower_half
  · have hindex := index.isLt
    omega
  · have hindex := index.isLt
    omega

end Schubert.Dihedral
