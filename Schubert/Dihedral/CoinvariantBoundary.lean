import Schubert.FiniteGroupCharacters.CharacterLine
import Schubert.Dihedral.CoinvariantDegreeSpans
import Schubert.Dihedral.CoinvariantGradedRepresentation
import Schubert.Dihedral.CoinvariantAxialAction
import Schubert.Dihedral.ScalarCharacters
import TauCeti.RepresentationTheory.CharacterTable.Determined

/-! # The constant and top coinvariant degree representations -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral.Coinvariant

/-- The degree-zero coinvariant character is the trivial character. -/
theorem character_zero (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (coinvariantPieceFDRep n 0).character element = 1 := by
  let piece := TauCeti.GradedAlgebra.quotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) 0
  have hmem : (1 : CoinvariantAlgebra n) ∈ piece := by
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    exact MvPolynomial.isHomogeneous_one (Fin 2) ℂ
  let vector : piece := ⟨1, hmem⟩
  have hnonzero : vector ≠ 0 := by
    intro hequal
    exact coinvariant_one_ne_zero n hthree (congrArg Subtype.val hequal)
  have hspan : Submodule.span ℂ {vector} = ⊤ := by
    have hspanning := (Submodule.span_range_subtype_eq_top_iff piece
      (s := fun _ : Fin 1 => (1 : CoinvariantAlgebra n)) (fun _ => hmem)).mpr
      (by simpa using (Piece.eq_span_zero n hthree).symm)
    simpa [vector] using hspanning
  rw [coinvariantPieceFDRep_character]
  apply Schubert.FiniteGroupCharacters.character_line
    (coinvariantPieceRepresentation n 0) vector hnonzero hspan element 1
  apply Subtype.ext
  change coinvariantAction n element 1 = (1 : ℂ) • (1 : CoinvariantAlgebra n)
  simp only [map_one, one_smul]

/-- The constant coinvariant degree is isomorphic to the trivial representation. -/
theorem zero_iso (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Nonempty (coinvariantPieceFDRep n 0 ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [character_zero n hthree, FDRep.character_of_trivial]

/-- The top coinvariant character is the determinant sign character. -/
theorem character_top (n : ℕ) [NeZero n] (hthree : 3 ≤ n) (element : DihedralGroup n) :
    (coinvariantPieceFDRep n n).character element = signCharacter n element := by
  let piece := TauCeti.GradedAlgebra.quotientPiece
    (MvPolynomial.homogeneousSubmodule (Fin 2) ℂ) (coinvariantIdeal n) n
  have hmem : Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n) ∈ piece := by
    apply TauCeti.GradedAlgebra.mk_mem_quotientPiece
    simpa using auxiliaryU_isHomogeneous.pow n
  let vector : piece := ⟨Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n), hmem⟩
  have hnonzero : vector ≠ 0 := by
    intro hequal
    exact coinvariant_top_axial_ne_zero n hthree (congrArg Subtype.val hequal)
  have hspan : Submodule.span ℂ {vector} = ⊤ := by
    have hspanning := (Submodule.span_range_subtype_eq_top_iff piece
      (s := fun _ : Fin 1 => Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n))
      (fun _ => hmem)).mpr
      (by simpa using (coinvariant_homogeneousPiece_eq_span_top n hthree).symm)
    simpa [vector] using hspanning
  rw [coinvariantPieceFDRep_character]
  apply Schubert.FiniteGroupCharacters.character_line
    (coinvariantPieceRepresentation n n) vector hnonzero hspan element (signCharacter n element)
  apply Subtype.ext
  change coinvariantRepresentation n element
      (Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n)) =
    signCharacter n element • Ideal.Quotient.mk (coinvariantIdeal n) (auxiliaryU ^ n)
  rw [coinvariantRepresentation_mk]
  cases element with
  | r coordinate =>
      rw [signCharacter_r, one_smul, polynomialAction_r_top_auxiliaryU n hthree]
  | sr coordinate =>
      rw [signCharacter_sr]
      simpa only [map_pow, neg_one_smul] using coinvariant_sr_top n hthree coordinate

/-- The top coinvariant degree is isomorphic to the determinant sign object. -/
theorem top_iso (n : ℕ) [NeZero n] (hthree : 3 ≤ n) :
    Nonempty (coinvariantPieceFDRep n n ≅ signFDRep n) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [character_top n hthree, signFDRep_character]

end Schubert.Dihedral.Coinvariant
