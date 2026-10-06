import Schubert.Dihedral.ScalarMultiplicity

/-! # Exact standard scalar-slot morphism dimensions -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral
variable {n : ℕ} [NeZero n]

/-- Scalar slots have Kronecker morphism multiplicities. -/
theorem scalar_hom_slot (first second : Fin (if Even n then 4 else 2)) :
    Module.finrank ℂ (scalarFDRep n first ⟶ scalarFDRep n second) =
      if first.val = second.val then 1 else 0 := by
  classical
  let : Simple (scalarFDRep n first) := scalarFDRep_simple n first
  let : Simple (scalarFDRep n second) := scalarFDRep_simple n second
  rw [FDRep.finrank_hom_simple_simple]
  simp only [ScalarFamily.iso_iff_eq, Fin.ext_iff]

/-- The trivial object occupies exactly the zero scalar slot. -/
theorem scalar_hom_trivial (scalar : Fin (if Even n then 4 else 2)) :
    Module.finrank ℂ (scalarFDRep n scalar ⟶
      FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) =
      if scalar.val = 0 then 1 else 0 := by
  let zero : Fin (if Even n then 4 else 2) := ⟨0, by split_ifs <;> omega⟩
  have hzero : scalarFDRep n zero = FDRep.of
      (Representation.trivial ℂ (DihedralGroup n) ℂ) := by simp [scalarFDRep, zero]
  rw [← hzero, scalar_hom_slot]

/-- Each additional even character occupies exactly its designated scalar slot. -/
theorem scalar_hom_even_slot (scalar : Fin (if Even n then 4 else 2))
    (heven : Even n) (negative : Bool) :
    Module.finrank ℂ (scalarFDRep n scalar ⟶ evenScalarFDRep n heven negative) =
      if scalar.val = (if negative then 3 else 2) then 1 else 0 := by
  let selected : Fin (if Even n then 4 else 2) :=
    ⟨if negative then 3 else 2, by simp only [heven, ite_true]; cases negative <;> decide⟩
  have hselected : scalarFDRep n selected = evenScalarFDRep n heven negative := by
    cases negative <;> simp [scalarFDRep, selected, heven]
  rw [← hselected, scalar_hom_slot]

end Schubert.Dihedral
