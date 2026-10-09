import DihedralHessenberg.Dihedral.ScalarFamily
import DihedralHessenberg.FiniteGroupCharacters.SimpleFamily
import Mathlib.RepresentationTheory.Maschke

/-! # Completeness of the dihedral irreducible family -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral

/-- Members of the finite irreducible family are isomorphic exactly at equal indices. -/
theorem irrepFDRep_iso_iff_eq (n : ℕ) [NeZero n] (first second : IrrepIndex n) :
    Nonempty (irrepFDRep n first ≅ irrepFDRep n second) ↔ first = second := by
  constructor
  · intro hisomorphism
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            change Nonempty (scalarFDRep n first ≅ scalarFDRep n second) at hisomorphism
            exact congrArg Sum.inl ((ScalarFamily.iso_iff_eq n first second).mp hisomorphism)
        | inr second =>
            exact (ScalarFamily.not_frequency_iso n first _ hisomorphism).elim
    | inr first =>
        cases second with
        | inl second =>
            obtain ⟨isomorphism⟩ := hisomorphism
            exact (ScalarFamily.not_frequency_iso n second _ ⟨isomorphism.symm⟩).elim
        | inr second =>
            change Nonempty (frequencyFDRep n (first.val + 1 : ℕ) ≅
              frequencyFDRep n (second.val + 1 : ℕ)) at hisomorphism
            have hfirst : 2 * (first.val + 1) < n := by
              have hbound := first.isLt
              omega
            have hsecond : 2 * (second.val + 1) < n := by
              have hbound := second.isLt
              omega
            have hequal :=
              (frequencyFDRep_iso_iff_frequency_eq n _ _ hfirst hsecond).mp hisomorphism
            apply congrArg Sum.inr
            apply Fin.ext
            omega
  · rintro rfl
    exact ⟨Iso.refl _⟩

/-- Every simple standard dihedral representation is a member of the finite family. -/
theorem irrepFDRep_complete (n : ℕ) [NeZero n] (object : FDRep ℂ (DihedralGroup n))
    [Simple object] : ∃ index, Nonempty (irrepFDRep n index ≅ object) := by
  apply Schubert.FiniteGroupCharacters.SimpleFamily.complete (irrepFDRep n)
  · exact irrepFDRep_simple n
  · intro first second hisomorphism
    exact (irrepFDRep_iso_iff_eq n first second).mp hisomorphism
  · exact (irrepIndex_card n).ge

/-- An irreducible standard dihedral representation has dimension one or two. -/
theorem simple_finrank_one_or_two (n : ℕ) [NeZero n] (object : FDRep ℂ (DihedralGroup n))
    [Simple object] : Module.finrank ℂ object = 1 ∨ Module.finrank ℂ object = 2 := by
  obtain ⟨index, ⟨isomorphism⟩⟩ := irrepFDRep_complete n object
  have hdimension := congrFun (FDRep.char_iso isomorphism) (1 : DihedralGroup n)
  rw [FDRep.char_one, FDRep.char_one] at hdimension
  cases index with
  | inl index =>
      change (Module.finrank ℂ (scalarFDRep n index) : ℂ) = _ at hdimension
      rw [ScalarFamily.finrank] at hdimension
      left
      exact_mod_cast hdimension.symm
  | inr index =>
      change (Module.finrank ℂ (frequencyFDRep n (index.val + 1 : ℕ)) : ℂ) = _ at hdimension
      rw [frequencyFDRep_finrank] at hdimension
      right
      exact_mod_cast hdimension.symm

end Schubert.Dihedral
