import DihedralHessenberg.Dihedral.ScalarCharacterFacts
import DihedralHessenberg.Dihedral.FrequencyDistinction
import DihedralHessenberg.Dihedral.ConjugacyCount

/-! # A finite family of scalar and positive lower-half dihedral representations -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral

/-- The scalar slots and positive lower-half frequencies of the dihedral family. -/
abbrev IrrepIndex (n : ℕ) :=
  Fin (if Even n then 4 else 2) ⊕ Fin ((n - 1) / 2)

/-- The scalar slots are trivial, sign, and the two additional even-order characters. -/
def scalarFDRep (n : ℕ) [NeZero n] (index : Fin (if Even n then 4 else 2)) :
    FDRep ℂ (DihedralGroup n) :=
  if index.val = 0 then FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)
  else if index.val = 1 then signFDRep n
  else if heven : Even n then evenScalarFDRep n heven (decide (index.val = 3))
  else FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)

/-- The finite family uses scalar objects and the defining frequency pullbacks. -/
def irrepFDRep (n : ℕ) [NeZero n] : IrrepIndex n → FDRep ℂ (DihedralGroup n)
  | .inl index => scalarFDRep n index
  | .inr index => frequencyFDRep n (index.val + 1 : ℕ)

/-- Every scalar slot is simple. -/
theorem scalarFDRep_simple (n : ℕ) [NeZero n]
    (index : Fin (if Even n then 4 else 2)) : Simple (scalarFDRep n index) := by
  by_cases hzero : index.val = 0
  · rw [scalarFDRep, ite_eq_left hzero]
    apply (FDRep.simple_iff_isIrreducible _).mpr
    change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
    infer_instance
  · by_cases hone : index.val = 1
    · rw [scalarFDRep, ite_eq_right hzero, ite_eq_left hone]
      exact signFDRep_simple n
    · by_cases heven : Even n
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_left heven]
        exact evenScalarFDRep_simple n heven _
      · rw [scalarFDRep, ite_eq_right hzero, ite_eq_right hone, dite_eq_right heven]
        apply (FDRep.simple_iff_isIrreducible _).mpr
        change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
        infer_instance

/-- Every member of the finite dihedral family is simple. -/
theorem irrepFDRep_simple (n : ℕ) [NeZero n] (index : IrrepIndex n) :
    Simple (irrepFDRep n index) := by
  cases index with
  | inl index =>
      change Simple (scalarFDRep n index)
      exact scalarFDRep_simple n index
  | inr index =>
      change Simple (frequencyFDRep n (index.val + 1 : ℕ))
      exact frequencyFDRep_simple_of_lower_half n (index.val + 1) (by omega) (by
        have hbound := index.isLt
        omega)

/-- The family has exactly as many indices as the group has conjugacy classes. -/
theorem irrepIndex_card (n : ℕ) [NeZero n] :
    Nat.card (IrrepIndex n) = Nat.card (ConjClasses (DihedralGroup n)) := by
  change Nat.card (Fin (if Even n then 4 else 2) ⊕ Fin ((n - 1) / 2)) = _
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin, card_conjClasses_piecewise]
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases heven : Even n
  · simp only [heven, ↓reduceIte]
    obtain ⟨half, hhalf⟩ := heven
    omega
  · simp only [heven, ↓reduceIte]
    obtain ⟨half, hhalf⟩ := Nat.not_even_iff_odd.mp heven
    omega

end Schubert.Dihedral
