import Schubert.FiniteGroupCharacters.MultiplicityExhaustion
import Schubert.Dihedral.IrrepDimensionCounts

/-! # Complete effective expansions of dihedral representations -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n]

/-- The complete scalar and frequency family expands every dihedral class. -/
theorem irrep_class_expansion (source : FDRep ℂ (DihedralGroup n)) :
    (TauCeti.SplitK0.of source : TauCeti.repRing ℂ (DihedralGroup n)) =
      ∑ index, Module.finrank ℂ (irrepFDRep n index ⟶ source) •
        TauCeti.SplitK0.of (irrepFDRep n index) :=
  SimpleFamily.class_expansion (irrepFDRep n) (irrepFDRep_simple n)
    (fun first second => (irrepFDRep_iso_iff_eq n first second).mp) (irrepIndex_card n) source

/-- Scalar and frequency multiplicities account for the entire carrier dimension. -/
theorem irrep_dimension_sum (source : FDRep ℂ (DihedralGroup n)) :
    Module.finrank ℂ source = ∑ index, Module.finrank ℂ (irrepFDRep n index ⟶ source) *
      Sum.elim (fun _ => 1) (fun _ => 2) index := by
  rw [SimpleFamily.dimension_sum (irrepFDRep n) (irrepFDRep_simple n)
    (fun first second => (irrepFDRep_iso_iff_eq n first second).mp) (irrepIndex_card n)]
  simp only [irrepFDRep_finrank]

/-- Saturated lower bounds force every dihedral constituent multiplicity. -/
theorem irrep_multiplicities_exhausted (source : FDRep ℂ (DihedralGroup n))
    (lower : IrrepIndex n → ℕ)
    (hlower : ∀ index, lower index ≤ Module.finrank ℂ (irrepFDRep n index ⟶ source))
    (hbudget : ∑ index, lower index * Sum.elim (fun _ => 1) (fun _ => 2) index =
      Module.finrank ℂ source) :
    ∀ index, Module.finrank ℂ (irrepFDRep n index ⟶ source) = lower index := by
  apply SimpleFamily.multiplicities_exhausted (irrepFDRep n) (irrepFDRep_simple n)
    (fun first second => (irrepFDRep_iso_iff_eq n first second).mp) (irrepIndex_card n)
    source lower
  · intro index
    rw [irrepFDRep_finrank]
    cases index <;> norm_num
  · exact hlower
  · simpa only [irrepFDRep_finrank] using hbudget

end Schubert.Dihedral
