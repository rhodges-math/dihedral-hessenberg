import Schubert.DihedralSplines.CoSubrepresentation

/-! # The reflected coinvariant graded subrepresentation in all degrees -/

noncomputable section
open CategoryTheory
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The quotient invariant range, extended by the zero subspace above the top degree. -/
def coRange (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) :
    Subrepresentation (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree) :=
  if hdegree : degree ≤ ideal.carrier.ncard then
    coSubpiece ideal hproper ⟨degree, Nat.lt_succ_of_le hdegree⟩
  else ⊥

/-- Above the selected cardinality the invariant subspace is zero. -/
theorem coRange_above (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ)
    (habove : ideal.carrier.ncard < degree) : coRange ideal hproper degree = ⊥ := by
  rw [coRange, dite_eq_right habove.not_ge]

/-- The degreewise finite objects carry the inherited action on the quotient subspaces. -/
def coGradedRepresentation (hproper : ideal.carrier ≠ positiveRoots n) :
    GradedRepresentation ℂ (DihedralGroup n) := fun degree => by
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (coRange ideal hproper degree).toSubmodule := Submodule.addCommGroup _
  let : Module ℂ (coRange ideal hproper degree).toSubmodule := Submodule.module _
  exact FDRep.of (coRange ideal hproper degree).toRepresentation

/-- Every bounded degree is the invariant-range constituent object. -/
theorem coGradedRepresentation_below (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    coGradedRepresentation ideal hproper degree =
      coSubpieceFDRep ideal hproper ⟨degree, Nat.lt_succ_of_le hdegree⟩ := by
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let bundle (subspace : Subrepresentation
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree)) :
      FDRep ℂ (DihedralGroup n) := FDRep.of subspace.toRepresentation
  change bundle (coRange ideal hproper degree) =
    bundle (coSubpiece ideal hproper ⟨degree, Nat.lt_succ_of_le hdegree⟩)
  apply congrArg bundle
  exact dite_eq_left hdegree

/-- The inherited action has zero character above the top degree. -/
theorem coGradedRepresentation_above (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    (TauCeti.SplitK0.of (coGradedRepresentation ideal hproper degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = 0 := by
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let : AddCommGroup (coRange ideal hproper degree).toSubmodule := Submodule.addCommGroup _
  let : Module ℂ (coRange ideal hproper degree).toSubmodule := Submodule.module _
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of, map_zero]
  funext element
  change Representation.character (coRange ideal hproper degree).toRepresentation element = 0
  let : Subsingleton (coRange ideal hproper degree).toSubmodule := by
    apply Submodule.subsingleton_iff_eq_bot.mpr
    exact congrArg Subrepresentation.toSubmodule (coRange_above ideal hproper degree habove)
  have hoperator : (coRange ideal hproper degree).toRepresentation element = 0 :=
    Subsingleton.elim _ _
  rw [Representation.character, hoperator, map_zero]

/-- The all-natural-degree graded subrepresentation has the exact Co_H series. -/
theorem coGradedRepresentation_class (hproper : ideal.carrier ≠ positiveRoots n) :
    gradedClass (coGradedRepresentation ideal hproper) = ideal.coClass := by
  ext degree
  rw [gradedClass_coeff]
  by_cases hdegree : degree ≤ ideal.carrier.ncard
  · rw [coGradedRepresentation_below ideal hproper degree hdegree]
    exact coSubpiece_class ideal hproper ⟨degree, Nat.lt_succ_of_le hdegree⟩
  · rw [coGradedRepresentation_above ideal hproper degree (by omega),
      coClass_coeff_above ideal degree (by omega)]

/-- Inclusion of each inherited invariant range into the quotient degree. -/
def coInclusion (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) :
    Representation.IntertwiningMap (coGradedRepresentation ideal hproper degree).ρ
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree) := by
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree) := Submodule.module _
  exact { toLinearMap := (coRange ideal hproper degree).toSubmodule.subtype
          isIntertwining' := fun _ => rfl }

/-- Every graded inclusion is injective on its quotient-subspace carrier. -/
theorem coInclusion_injective (hproper : ideal.carrier ≠ positiveRoots n) (degree : ℕ) :
    Function.Injective (coInclusion ideal hproper degree) := Subtype.val_injective

/-- The graded invariant quotient subspaces realize Co_H, with zero pieces above the top. -/
theorem co_subrepresentation (hproper : ideal.carrier ≠ positiveRoots n) :
    (∀ degree, Function.Injective (coInclusion ideal hproper degree)) ∧
      (∀ degree, ideal.carrier.ncard < degree → coRange ideal hproper degree = ⊥) ∧
      gradedClass (coGradedRepresentation ideal hproper) = ideal.coClass :=
  ⟨coInclusion_injective ideal hproper, coRange_above ideal hproper,
    coGradedRepresentation_class ideal hproper⟩

end Schubert.DihedralSplines.HessenbergIdeal.Right
