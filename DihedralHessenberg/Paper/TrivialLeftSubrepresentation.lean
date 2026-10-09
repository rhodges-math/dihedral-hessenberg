import DihedralHessenberg.Paper.TrivialLeftEmbedding
import DihedralHessenberg.FiniteGroupCharacters.IntertwinerRange
import DihedralHessenberg.FiniteGroupCharacters.GeometricSeries

/-! # The full graded trivial subrepresentation of the left quotient -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Left
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- A chosen injective map of the endpoint or doubled trivial object into its degree. -/
def trivialEmbedding (degree : Fin (ideal.carrier.ncard + 1)) :
    Representation.IntertwiningMap (trivialSource ideal degree.val).ρ
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree.val) :=
  (trivialSource_embedding ideal degree.val (Nat.le_of_lt_succ degree.isLt)).choose

/-- The constituent embedding is injective on its source carrier. -/
theorem trivialEmbedding_injective (degree : Fin (ideal.carrier.ncard + 1)) :
    Function.Injective (trivialEmbedding ideal degree) :=
  (trivialSource_embedding ideal degree.val (Nat.le_of_lt_succ degree.isLt)).choose_spec

/-- The bounded invariant range has the quotient action. -/
def trivialSubpiece (degree : Fin (ideal.carrier.ncard + 1)) :
    Subrepresentation
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree.val) :=
  (trivialEmbedding ideal degree).range

/-- The finite representation on the bounded quotient-subspace carrier. -/
def trivialSubpieceFDRep (degree : Fin (ideal.carrier.ncard + 1)) :
    FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree.val) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree.val) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (trivialSubpiece ideal degree).toSubmodule := Submodule.addCommGroup _
  let : Module ℂ (trivialSubpiece ideal degree).toSubmodule := Submodule.module _
  exact FDRep.of (trivialSubpiece ideal degree).toRepresentation

/-- The inherited range action is isomorphic to the specified trivial sum. -/
theorem trivialSubpiece_iso (degree : Fin (ideal.carrier.ncard + 1)) :
    Nonempty (trivialSource ideal degree.val ≅ trivialSubpieceFDRep ideal degree) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨rangeActionEquiv (trivialEmbedding ideal degree)
    (trivialEmbedding_injective ideal degree)⟩

/-- The trivial source has one endpoint class and two interior classes. -/
theorem trivialSource_class (degree : ℕ) :
    (TauCeti.SplitK0.of (trivialSource ideal degree) : TauCeti.repRing ℂ (DihedralGroup n)) =
      if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else 2 := by
  apply TauCeti.repRingCharacter_injective
  rw [TauCeti.repRingCharacter_of]
  funext element
  by_cases hendpoint : degree = 0 ∨ degree = ideal.carrier.ncard
  · simp [trivialSource, hendpoint, finiteSum_character]
  · simp [trivialSource, hendpoint, finiteSum_character, map_ofNat]

/-- The invariant subspace in every degree, with zero extension above the top. -/
def trivialRange (degree : ℕ) :
    Subrepresentation (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree) :=
  if hdegree : degree ≤ ideal.carrier.ncard then
    trivialSubpiece ideal ⟨degree, Nat.lt_succ_of_le hdegree⟩
  else ⊥

/-- All pieces above the top degree are the zero quotient subspace. -/
theorem trivialRange_above (degree : ℕ) (habove : ideal.carrier.ncard < degree) :
    trivialRange ideal degree = ⊥ := by
  rw [trivialRange, dite_eq_right habove.not_ge]

/-- The all-natural-degree family retains the inherited action on each range. -/
def trivialGradedRepresentation : GradedRepresentation ℂ (DihedralGroup n) := fun degree => by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (trivialRange ideal degree).toSubmodule := Submodule.addCommGroup _
  let : Module ℂ (trivialRange ideal degree).toSubmodule := Submodule.module _
  exact FDRep.of (trivialRange ideal degree).toRepresentation

private theorem graded_below (degree : ℕ) (hdegree : degree ≤ ideal.carrier.ncard) :
    trivialGradedRepresentation ideal degree =
      trivialSubpieceFDRep ideal ⟨degree, Nat.lt_succ_of_le hdegree⟩ := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  let := RootSubset.Left.quotient_finite ideal.toRootSubset hthree
  let bundle (subspace : Subrepresentation
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree)) :
      FDRep ℂ (DihedralGroup n) := FDRep.of subspace.toRepresentation
  change bundle (trivialRange ideal degree) =
    bundle (trivialSubpiece ideal ⟨degree, Nat.lt_succ_of_le hdegree⟩)
  apply congrArg bundle
  exact dite_eq_left hdegree

/-- Every invariant range has the endpoint, interior, or zero class. -/
theorem trivialGradedRepresentation_coeff (degree : ℕ) :
    (TauCeti.SplitK0.of (trivialGradedRepresentation ideal degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) =
        if degree = 0 ∨ degree = ideal.carrier.ncard then 1
        else if degree < ideal.carrier.ncard then 2 else 0 := by
  by_cases hdegree : degree ≤ ideal.carrier.ncard
  · rw [graded_below ideal degree hdegree,
      ← TauCeti.SplitK0.of_congr (trivialSubpiece_iso ideal
        ⟨degree, Nat.lt_succ_of_le hdegree⟩).some, trivialSource_class]
    change (if degree = 0 ∨ degree = ideal.carrier.ncard then 1 else 2) = _
    split_ifs <;> first | rfl | omega
  · have habove : ideal.carrier.ncard < degree := by omega
    simp only [show degree ≠ 0 by omega, show degree ≠ ideal.carrier.ncard by omega,
      show ¬ degree < ideal.carrier.ncard by omega, or_self, ite_false]
    let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
      Submodule.addCommGroup _
    let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
    let : AddCommGroup (trivialRange ideal degree).toSubmodule := Submodule.addCommGroup _
    let : Module ℂ (trivialRange ideal degree).toSubmodule := Submodule.module _
    apply TauCeti.repRingCharacter_injective
    rw [TauCeti.repRingCharacter_of, map_zero]
    funext element
    change Representation.character (trivialRange ideal degree).toRepresentation element = 0
    let : Subsingleton (trivialRange ideal degree).toSubmodule := by
      apply Submodule.subsingleton_iff_eq_bot.mpr
      exact congrArg Subrepresentation.toSubmodule (trivialRange_above ideal degree habove)
    have hoperator : (trivialRange ideal degree).toRepresentation element = 0 :=
      Subsingleton.elim _ _
    rw [Representation.character, hoperator, map_zero]

/-- The whole graded subrepresentation has the displayed doubled geometric class. -/
theorem trivialGradedRepresentation_class :
    gradedClass (trivialGradedRepresentation ideal) =
      (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range ideal.carrier.ncard,
        (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent := by
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed] at hminimum
  ext degree
  rw [gradedClass_coeff, trivialGradedRepresentation_coeff,
    geometric_double_coeff _ _ (by omega)]

/-- Inclusion of every invariant range into its quotient degree. -/
def trivialInclusion (degree : ℕ) :
    Representation.IntertwiningMap (trivialGradedRepresentation ideal degree).ρ
      (RootSubset.Left.pieceRepresentation ideal.toRootSubset hthree degree) := by
  let : AddCommGroup (RootSubset.Left.piece ideal.toRootSubset hthree degree) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Left.piece ideal.toRootSubset hthree degree) := Submodule.module _
  exact { toLinearMap := (trivialRange ideal degree).toSubmodule.subtype
          isIntertwining' := fun _ => rfl }

/-- Every graded-subspace inclusion is injective. -/
theorem trivialInclusion_injective (degree : ℕ) :
    Function.Injective (trivialInclusion ideal degree) := Subtype.val_injective

/-- The quotient contains the full displayed graded trivial subrepresentation. -/
theorem trivial_subrepresentation :
    (∀ degree : Fin (ideal.carrier.ncard + 1),
      Nonempty (trivialSource ideal degree.val ≅ trivialSubpieceFDRep ideal degree)) ∧
    (∀ degree, Function.Injective (trivialInclusion ideal degree)) ∧
      (∀ degree, ideal.carrier.ncard < degree → trivialRange ideal degree = ⊥) ∧
      gradedClass (trivialGradedRepresentation ideal) =
        (1 + PowerSeries.X) * ∑ exponent ∈ Finset.range ideal.carrier.ncard,
          (PowerSeries.X : PowerSeries (TauCeti.repRing ℂ (DihedralGroup n))) ^ exponent :=
  ⟨trivialSubpiece_iso ideal, trivialInclusion_injective ideal, trivialRange_above ideal,
    trivialGradedRepresentation_class ideal⟩

end Schubert.DihedralSplines.HessenbergIdeal.Left
