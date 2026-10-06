import Schubert.Dihedral.IrreducibleClassification
import Schubert.FiniteGroupCharacters.IrreducibleFinite

/-! # Finite-dimensional irreducible dihedral representations -/

noncomputable section

open CategoryTheory

namespace Schubert.Dihedral

/-- Every finite-dimensional irreducible dihedral action is equivalent to a family member. -/
theorem irreducible_equiv_family (n : ℕ) [NeZero n] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (action : Representation ℂ (DihedralGroup n) V) (hirreducible : action.IsIrreducible) :
    ∃ index, Nonempty (Representation.Equiv (irrepFDRep n index).ρ action) := by
  let equivalence := (FDRep.ofShrinkEquiv action).symm
  have hirreducible' : Representation.IsIrreducible (FDRep.ofShrink action).ρ :=
    TauCeti.Representation.isIrreducible_of_linearEquiv equivalence.toLinearEquiv
      (fun element vector => Representation.IntertwiningMap.isIntertwining
        action (FDRep.ofShrink action).ρ equivalence.toIntertwiningMap element vector)
      hirreducible
  let : Simple (FDRep.ofShrink action) :=
    (FDRep.simple_iff_isIrreducible _).mpr hirreducible'
  obtain ⟨index, hisomorphism⟩ := irrepFDRep_complete n (FDRep.ofShrink action)
  obtain ⟨familyEquivalence⟩ := TauCeti.nonempty_fdRepIso_iff.mp hisomorphism
  exact ⟨index, ⟨familyEquivalence.trans (FDRep.ofShrinkEquiv action)⟩⟩

/-- Every finite-dimensional irreducible dihedral action has dimension one or two. -/
theorem irreducible_finrank_one_or_two (n : ℕ) [NeZero n] {V : Type*}
    [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (action : Representation ℂ (DihedralGroup n) V) (hirreducible : action.IsIrreducible) :
    Module.finrank ℂ V = 1 ∨ Module.finrank ℂ V = 2 := by
  obtain ⟨index, ⟨equivalence⟩⟩ := irreducible_equiv_family n action hirreducible
  have hdimension := equivalence.toLinearEquiv.finrank_eq
  cases index with
  | inl index =>
      change Module.finrank ℂ (scalarFDRep n index) = _ at hdimension
      rw [ScalarFamily.finrank] at hdimension
      exact Or.inl hdimension.symm
  | inr index =>
      change Module.finrank ℂ (frequencyFDRep n (index.val + 1 : ℕ)) = _ at hdimension
      rw [frequencyFDRep_finrank] at hdimension
      exact Or.inr hdimension.symm

/-- Every irreducible dihedral action is equivalent to a unique finite-family member. -/
theorem irreducible_classification (n : ℕ) [NeZero n] {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (action : Representation ℂ (DihedralGroup n) V) (hirreducible : action.IsIrreducible) :
    ∃! index, Nonempty (Representation.Equiv (irrepFDRep n index).ρ action) := by
  let := Schubert.FiniteGroupCharacters.irreducible_finite action hirreducible
  obtain ⟨index, ⟨equivalence⟩⟩ := irreducible_equiv_family n action hirreducible
  refine ⟨index, ⟨equivalence⟩, ?_⟩
  intro other ⟨otherEquivalence⟩
  apply (irrepFDRep_iso_iff_eq n other index).mp
  exact TauCeti.nonempty_fdRepIso_iff.mpr ⟨otherEquivalence.trans equivalence.symm⟩

/-- Every irreducible dihedral action has dimension one or two. -/
theorem irreducible_dimension (n : ℕ) [NeZero n] {V : Type*}
    [AddCommGroup V] [Module ℂ V]
    (action : Representation ℂ (DihedralGroup n) V) (hirreducible : action.IsIrreducible) :
    Module.finrank ℂ V = 1 ∨ Module.finrank ℂ V = 2 := by
  let := Schubert.FiniteGroupCharacters.irreducible_finite action hirreducible
  exact irreducible_finrank_one_or_two n action hirreducible

end Schubert.Dihedral
