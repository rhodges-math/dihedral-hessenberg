import Schubert.DihedralSplines.QuotientDuality
import Schubert.DihedralSplines.TopRepresentation
import Schubert.Dihedral.SelfDual

/-! # Complementary quotient representations and the determinant twist -/

noncomputable section
open CategoryTheory
open scoped MonoidalCategory
namespace Schubert.DihedralSplines.HessenbergIdeal
open Schubert.Dihedral
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

namespace Left
/-- Complementary left quotient degrees are isomorphic representations. -/
theorem complementary_iso (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree ≅
      RootSubset.Left.pieceFDRep ideal.toRootSubset hthree (ideal.carrier.ncard - degree)) := by
  let complement := RootSubset.Left.pieceFDRep ideal.toRootSubset hthree
    (ideal.carrier.ncard - degree)
  let equivalence := (complementary_dual_iso ideal degree hdegree).some.trans
    (MonoidalCategory.tensorIso (self_dual complement).some.symm (top_iso ideal).some)
  have hunit : Nonempty (complement ⊗ FDRep.of
      (Representation.trivial ℂ (DihedralGroup n) ℂ) ≅ complement) := by
    apply FDRep.nonempty_iso_of_character_eq
    funext element
    rw [FDRep.char_tensor, Pi.mul_apply]
    simp
  exact ⟨equivalence.trans hunit.some⟩
/-- The complementary left degree is the dual of the given degree. -/
theorem complementary_dual (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree) ≅ FDRep.of (Representation.dual
        (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree).ρ)) := by
  exact ⟨(complementary_iso ideal degree hdegree).some.symm.trans
    (self_dual (RootSubset.Left.pieceFDRep ideal.toRootSubset hthree degree)).some⟩

end Left

namespace Right
/-- Complementary right quotient degrees differ by the determinant tensor. -/
theorem complementary_sign_iso (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree ≅
      RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
        (ideal.carrier.ncard - degree) ⊗ signFDRep n) := by
  let complement := RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
    (ideal.carrier.ncard - degree)
  exact ⟨(complementary_dual_iso ideal degree hdegree).some.trans
    (MonoidalCategory.tensorIso (self_dual complement).some.symm (top_iso ideal).some)⟩
/-- Determinant tensored on the left identifies the complementary right degree. -/
theorem sign_complementary (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    Nonempty (signFDRep n ⊗ RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
      (ideal.carrier.ncard - degree) ≅
        RootSubset.Right.pieceFDRep ideal.toRootSubset hthree degree) := by
  exact ⟨(β_ (signFDRep n) (RootSubset.Right.pieceFDRep ideal.toRootSubset hthree
    (ideal.carrier.ncard - degree))).trans
      (complementary_sign_iso ideal degree hdegree).some.symm⟩

end Right

end Schubert.DihedralSplines.HessenbergIdeal
