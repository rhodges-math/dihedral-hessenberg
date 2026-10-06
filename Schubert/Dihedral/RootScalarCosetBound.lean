import Schubert.Dihedral.ScalarCosetBound

/-! # The scalar constituent selected by a root coset -/

noncomputable section
open CategoryTheory
namespace Schubert.Dihedral
open Schubert.FiniteGroupCharacters
variable {n : ℕ} [NeZero n]

/-- The chosen root scalar character occurs in its coset representation. -/
theorem root_scalar_coset_bound (alpha : PositiveRoot n) (heven : Even n) :
    1 ≤ Module.finrank ℂ (alpha.scalarFDRep heven ⟶ alpha.cosetFDRep) := by
  classical
  let : Simple (alpha.scalarFDRep heven) := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_simple n heven _
  let : Simple (FDRep.of (Representation.trivial ℂ (DihedralGroup n) ℂ)) := by
    apply (FDRep.simple_iff_isIrreducible _).mpr
    change (Representation.trivial ℂ (DihedralGroup n) ℂ).IsIrreducible
    infer_instance
  have hdimension : Module.finrank ℂ (alpha.scalarFDRep heven) = 1 := by
    unfold PositiveRoot.scalarFDRep
    exact evenScalarFDRep_finrank n heven _
  rw [scalar_hom_coset _ hdimension, dite_eq_left heven]
  have hself : Module.finrank ℂ (alpha.scalarFDRep heven ⟶ alpha.scalarFDRep heven) = 1 := by
    rw [FDRep.finrank_hom_simple_simple]
    simp only [show Nonempty (alpha.scalarFDRep heven ≅ alpha.scalarFDRep heven)
      from ⟨Iso.refl _⟩, ite_true]
  rw [hself]
  omega

end Schubert.Dihedral
