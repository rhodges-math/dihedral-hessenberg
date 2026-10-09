import DihedralHessenberg.Paper.CoSourceEmbedding
import DihedralHessenberg.FiniteGroupCharacters.IntertwinerRange

/-! # Reflected coinvariant subrepresentations of the right quotient -/

noncomputable section
open CategoryTheory
open scoped BigOperators
namespace Schubert.DihedralSplines.HessenbergIdeal.Right
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- An injective constituent map into the right quotient degree. -/
def coEmbedding (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) :
    Representation.IntertwiningMap (coSource ideal degree.val).ρ
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree.val) :=
  (coSource_embedding ideal hproper degree.val (Nat.le_of_lt_succ degree.isLt)).choose

/-- The chosen map is injective on the constituent carrier. -/
theorem coEmbedding_injective (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) :
    Function.Injective (coEmbedding ideal hproper degree) :=
  (coSource_embedding ideal hproper degree.val (Nat.le_of_lt_succ degree.isLt)).choose_spec

/-- The invariant range inside the homogeneous right quotient. -/
def coSubpiece (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) :
    Subrepresentation
      (RootSubset.Right.pieceRepresentation ideal.toRootSubset hthree degree.val) :=
  (coEmbedding ideal hproper degree).range

/-- The inherited action on the reflected constituent range. -/
def coSubpieceFDRep (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) : FDRep ℂ (DihedralGroup n) := by
  let : AddCommGroup (RootSubset.Right.piece ideal.toRootSubset hthree degree.val) :=
    Submodule.addCommGroup _
  let : Module ℂ (RootSubset.Right.piece ideal.toRootSubset hthree degree.val) := Submodule.module _
  let := RootSubset.Right.quotient_finite ideal.toRootSubset hthree
  let : AddCommGroup (coSubpiece ideal hproper degree).toSubmodule := Submodule.addCommGroup _
  let : Module ℂ (coSubpiece ideal hproper degree).toSubmodule := Submodule.module _
  exact FDRep.of (coSubpiece ideal hproper degree).toRepresentation

/-- The invariant range is isomorphic to the specified reflected constituent. -/
theorem coSubpiece_iso (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) :
    Nonempty (coSource ideal degree.val ≅ coSubpieceFDRep ideal hproper degree) := by
  apply TauCeti.nonempty_fdRepIso_iff.mpr
  exact ⟨rangeActionEquiv (coEmbedding ideal hproper degree)
    (coEmbedding_injective ideal hproper degree)⟩

/-- The invariant range has the corresponding reflected class coefficient. -/
theorem coSubpiece_class (hproper : ideal.carrier ≠ positiveRoots n)
    (degree : Fin (ideal.carrier.ncard + 1)) :
    (TauCeti.SplitK0.of (coSubpieceFDRep ideal hproper degree) :
      TauCeti.repRing ℂ (DihedralGroup n)) = PowerSeries.coeff degree.val ideal.coClass := by
  rw [← TauCeti.SplitK0.of_congr (coSubpiece_iso ideal hproper degree).some]
  exact coSource_class ideal degree.val (Nat.le_of_lt_succ degree.isLt)

/-- The finite class series of the invariant quotient ranges is Co_H. -/
theorem coSubpiece_series (hproper : ideal.carrier ≠ positiveRoots n) :
    (∑ degree : Fin (ideal.carrier.ncard + 1),
      PowerSeries.monomial degree.val
        (TauCeti.SplitK0.of (coSubpieceFDRep ideal hproper degree) :
          TauCeti.repRing ℂ (DihedralGroup n))) = ideal.coClass := by
  simp_rw [coSubpiece_class]
  ext degree
  rw [map_sum]
  simp only [PowerSeries.coeff_monomial]
  by_cases hbelow : degree < ideal.carrier.ncard + 1
  · rw [Finset.sum_eq_single (⟨degree, hbelow⟩ : Fin (ideal.carrier.ncard + 1))]
    · simp
    · intro other _ hother
      have hne : other.val ≠ degree := by
        intro hequal
        exact hother (Fin.ext hequal)
      simp [Ne.symm hne]
    · simp
  · rw [coClass_coeff_above ideal degree (by omega)]
    apply Finset.sum_eq_zero
    intro other _
    have hne : other.val ≠ degree := by omega
    simp [Ne.symm hne]

end Schubert.DihedralSplines.HessenbergIdeal.Right
