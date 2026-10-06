import Schubert.FiniteGroupCharacters.DualEquiv
import Schubert.Dihedral.SelfDual
import Schubert.FiniteGroupCharacters.IrreducibleFinite

/-! # Inverse conjugacy and unrestricted irreducible self-duality -/

noncomputable section
namespace Schubert.Dihedral

/-- Every dihedral element is conjugate to its inverse. -/
theorem isConj_inv (n : ℕ) (element : DihedralGroup n) : IsConj element element⁻¹ := by
  cases element with
  | r coordinate =>
      rw [DihedralGroup.inv_r, isConj_r_iff]
      exact Or.inr rfl
  | sr coordinate =>
      simpa only [DihedralGroup.inv_sr] using IsConj.refl (DihedralGroup.sr coordinate)

/-- Every complex irreducible action, on any carrier, is equivalent to its dual. -/
theorem irreducible_self_dual (n : ℕ) [NeZero n] {V : Type*}
    [AddCommGroup V] [Module ℂ V] (action : Representation ℂ (DihedralGroup n) V)
    (hirreducible : action.IsIrreducible) :
    Nonempty (Representation.Equiv action action.dual) := by
  let := Schubert.FiniteGroupCharacters.irreducible_finite action hirreducible
  let shrink := FDRep.ofShrinkEquiv action
  obtain ⟨isomorphism⟩ := self_dual (FDRep.ofShrink action)
  obtain ⟨equivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp ⟨isomorphism⟩
  exact ⟨shrink.symm.trans
    (equivalence.trans (Schubert.FiniteGroupCharacters.dualEquiv shrink))⟩

end Schubert.Dihedral
