import DihedralHessenberg.Dihedral.ScalarMultiplicity
import DihedralHessenberg.Dihedral.SimpleScalar

/-! # Even scalar constituents of the paired simple-root cosets -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- Even scalar objects cannot be isomorphic to the trivial object. -/
theorem even_scalar_not_trivial (heven : Even n) (negative : Bool) :
    ¬ Nonempty (evenScalarFDRep n heven negative ≅
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
  rintro ⟨equivalence⟩
  have hcharacter := congrFun (FDRep.char_iso equivalence) (rotation n)
  rw [evenScalarFDRep_character, evenScalarCharacter_rotation,
    FDRep.character_of_trivial] at hcharacter
  norm_num at hcharacter

/-- Each extra even scalar constituent occurs in the paired simple-root cosets. -/
theorem even_scalar_coset_bound (hthree : 3 ≤ n) (heven : Even n) (negative : Bool) :
    1 ≤ Module.finrank ℂ (evenScalarFDRep n heven negative ⟶
      (simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep) := by
  classical
  let : Simple (evenScalarFDRep n heven negative) := evenScalarFDRep_simple n heven negative
  let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
    infer_instance
  have hzero : Module.finrank ℂ (evenScalarFDRep n heven negative ⟶
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) = 0 := by
    rw [FDRep.finrank_hom_simple_simple]
    simp only [even_scalar_not_trivial heven negative, ite_false]
  have hself : Module.finrank ℂ (evenScalarFDRep n heven negative ⟶
      evenScalarFDRep n heven negative) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]
    simp only [show Nonempty (evenScalarFDRep n heven negative ≅
      evenScalarFDRep n heven negative) from ⟨Iso.refl _⟩, ite_true]
  rw [hom_biprod_finrank, scalar_hom_coset _ (evenScalarFDRep_finrank n heven negative),
    scalar_hom_coset _ (evenScalarFDRep_finrank n heven negative), hzero,
    dite_eq_left heven, dite_eq_left heven, first_simple_scalar n hthree heven,
    second_simple_scalar n hthree heven]
  cases negative <;> simp only [zero_add] at hself ⊢
  all_goals rw [hself]; omega

end Schubert.Dihedral
