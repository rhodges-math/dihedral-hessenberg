import Schubert.Dihedral.RootCosetObjects
import TauCeti.RepresentationTheory.FDRep

/-! # Finite-dimensional root-reflection coset representations -/

noncomputable section

namespace Schubert.Dihedral.PositiveRoot

/-- The standard finite-dimensional object of the root-reflection coset action. -/
def cosetFDRep {n : ℕ} [NeZero n] (alpha : PositiveRoot n) :
    FDRep ℂ (DihedralGroup n) := FDRep.of alpha.cosetRepresentation

/-- Bundling the coset action preserves its character. -/
theorem cosetFDRep_character {n : ℕ} [NeZero n] (alpha : PositiveRoot n)
    (element : DihedralGroup n) :
    alpha.cosetFDRep.character element = alpha.cosetRepresentation.character element :=
  congrFun (FDRep.character_of _) element

/-- The coset representation has dimension equal to the number of cosets. -/
theorem cosetFDRep_finrank {n : ℕ} [NeZero n] (alpha : PositiveRoot n) :
    Module.finrank ℂ alpha.cosetFDRep = n := by
  classical
  let := Fintype.ofFinite alpha.Cosets
  change Module.finrank ℂ (MonoidAlgebra ℂ alpha.Cosets) = n
  rw [(MonoidAlgebra.coeffLinearEquiv ℂ).finrank_eq]
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card]
  exact alpha.card_cosets

end Schubert.Dihedral.PositiveRoot
