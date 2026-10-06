import Schubert.FiniteGroupCharacters.ScalarEigenline
import Schubert.Dihedral.SimpleEigenvector
import Schubert.DihedralSplines.TopQuotientAction
import Schubert.DihedralSplines.QuotientPairing
import Schubert.DihedralSplines.SingletonTranslation
import Schubert.Dihedral.ScalarCharacters
import Schubert.DihedralSplines.QuotientRepresentation

/-! # Trivial and determinant actions on the top quotient pieces -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left

/-- The top quotient action is the one-dimensional trivial action. -/
def topActionEquiv : Representation.Equiv
    (ScalarCharacter.representation (1 : DihedralGroup n →* ℂ))
    (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard) := by
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let vector : RootSubset.Left.piece ideal.toRootSubset hthree ideal.carrier.ncard :=
    ⟨RootSubset.Left.quotientMap ideal.toRootSubset hthree ideal.topSpline,
      (RootSubset.Left.mem_piece ideal.toRootSubset hthree _ _).mpr
        ⟨ideal.topSpline, ideal.topSpline_mem_piece, rfl⟩⟩
  have hnonzero : vector ≠ 0 := by
    intro hzero
    exact Left.top_class_ne_zero ideal (congrArg Subtype.val hzero)
  apply ScalarCharacter.eigenlineEquiv
    (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard)
    (1 : DihedralGroup n →* ℂ) vector hnonzero (FlowupSpline.Left.top_finrank ideal)
  apply eigenvector_of_simple hthree
  intro index
  have hsimple : simpleRoot n hthree index = simpleRoot n hthree 0 ∨
      simpleRoot n hthree index = simpleRoot n hthree 1 := by
    fin_cases index <;> simp
  have hvalue := Left.top_simple_fixed ideal (simpleRoot n hthree index) hsimple
  rw [simpleRoot_reflection] at hvalue
  apply Subtype.ext
  simp only [MonoidHom.one_apply, one_smul]
  exact hvalue

/-- The left top degree is a trivial representation object. -/
theorem top_iso : Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree
    ideal.carrier.ncard ≅ FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  apply FDRep.nonempty_iso_of_character_eq
  funext element
  rw [RootSubset.Left.pieceFDRep_character]
  have htrace := congrFun (Representation.char_iso (topActionEquiv ideal)) element
  rw [ScalarCharacter.character] at htrace
  rw [← htrace]
  simp

end Left

namespace Right

/-- The top quotient action is the one-dimensional determinant action. -/
def topActionEquiv : Representation.Equiv
    (ScalarCharacter.representation (signCharacter n))
    (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard) := by
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let vector : RootSubset.Right.piece ideal.toRootSubset hthree ideal.carrier.ncard :=
    ⟨RootSubset.Right.quotientMap ideal.toRootSubset hthree ideal.topSpline,
      (RootSubset.Right.mem_piece ideal.toRootSubset hthree _ _).mpr
        ⟨ideal.topSpline, ideal.topSpline_mem_piece, rfl⟩⟩
  have hnonzero : vector ≠ 0 := by
    intro hzero
    exact Right.top_class_ne_zero ideal (congrArg Subtype.val hzero)
  apply ScalarCharacter.eigenlineEquiv
    (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree ideal.carrier.ncard)
    (signCharacter n) vector hnonzero (FlowupSpline.Right.top_finrank ideal)
  apply eigenvector_of_simple hthree
  intro index
  have hsimple : simpleRoot n hthree index = simpleRoot n hthree 0 ∨
      simpleRoot n hthree index = simpleRoot n hthree 1 := by
    fin_cases index <;> simp
  have hvalue := Right.top_simple_negated ideal (simpleRoot n hthree index) hsimple
  rw [simpleRoot_reflection] at hvalue
  apply Subtype.ext
  have hsign : signCharacter n (simpleReflection n index) = -1 := by
    fin_cases index
    · change signCharacter n (.sr 0) = -1
      exact signCharacter_sr n 0
    · change signCharacter n (.sr 1) = -1
      exact signCharacter_sr n 1
  rw [hsign, neg_one_smul]
  exact hvalue

/-- The right top degree is the determinant representation object. -/
theorem top_iso : Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
    ideal.carrier.ncard ≅ signFDRep n) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨(topActionEquiv ideal).symm⟩

end Right

end Schubert.DihedralSplines.HessenbergIdeal
