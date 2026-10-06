import Schubert.FiniteGroupCharacters.PermutationSum
import Schubert.DihedralSplines.FlowupOrbitDegree
import Schubert.DihedralSplines.FlowupMiddleIndependence

/-! # Paired middle orbit representations -/

noncomputable section
open CategoryTheory Limits
namespace Schubert.DihedralSplines.FlowupSpline
open Schubert.Dihedral Schubert.FiniteGroupCharacters
variable {n : ℕ} {hthree : 3 ≤ n} [NeZero n] (ideal : HessenbergIdeal n hthree)

/-- The two prescribed-simple orbit-value families are jointly independent. -/
theorem middle_orbits_independent (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    letI := ideal.toRootSubset.dotMulAction hthree
    LinearIndependent ℂ (Sum.elim
      (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
        (value : ideal.toRootSubset.Spline))
      (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
        (value : ideal.toRootSubset.Spline))) := by
  classical
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal first.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal first.vertex)).fintype
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal second.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal second.vertex)).fintype
  let firstTranslate (value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex)) :=
    Classical.choose (MulAction.mem_orbit_iff.mp value.property)
  let secondTranslate (value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex)) :=
    Classical.choose (MulAction.mem_orbit_iff.mp value.property)
  have hfirst : ∀ value, ideal.toRootSubset.dot hthree (firstTranslate value)
      (spline ideal first.vertex) = value.val := fun value =>
    Classical.choose_spec (MulAction.mem_orbit_iff.mp value.property)
  have hsecond : ∀ value, ideal.toRootSubset.dot hthree (secondTranslate value)
      (spline ideal second.vertex) = value.val := fun value =>
    Classical.choose_spec (MulAction.mem_orbit_iff.mp value.property)
  have hfirstInjective : Function.Injective (fun value => ideal.toRootSubset.dot hthree
      (firstTranslate value) (spline ideal first.vertex)) := by
    intro left right hequal
    apply Subtype.ext
    rw [← hfirst left, ← hfirst right]
    exact hequal
  have hsecondInjective : Function.Injective (fun value => ideal.toRootSubset.dot hthree
      (secondTranslate value) (spline ideal second.vertex)) := by
    intro left right hequal
    apply Subtype.ext
    rw [← hsecond left, ← hsecond right]
    exact hequal
  have hindependent := paired_middle_independent ideal half hcard hproper first second
    firstTranslate secondTranslate hfirstInjective hsecondInjective
  have hfamily : Sum.elim
      (fun value => ideal.toRootSubset.dot hthree (firstTranslate value)
        (spline ideal first.vertex))
      (fun value => ideal.toRootSubset.dot hthree (secondTranslate value)
        (spline ideal second.vertex)) = Sum.elim
      (fun value => value.val) (fun value => value.val) := by
    funext index
    cases index with
    | inl value => exact hfirst value
    | inr value => exact hsecond value
  rw [hfamily] at hindependent
  exact hindependent

/-- The finite representation on the combined span of two middle orbits. -/
def middleOrbitFDRep (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    FDRep ℂ (DihedralGroup n) := by
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal first.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal first.vertex)).fintype
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal second.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal second.vertex)).fintype
  exact PermutationSpan.fdRep (ideal.toRootSubset.splineRepresentation hthree)
    (Sum.elim (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
      (value : ideal.toRootSubset.Spline))
      (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
        (value : ideal.toRootSubset.Spline)))
    (fun element index => by
      cases index with
      | inl value => exact (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm
      | inr value => exact (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    (middle_orbits_independent ideal half hcard hproper first second)


/-- Both simple-root coset objects act on the combined middle span. -/
theorem middle_coset_iso (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    Nonempty (((simpleRoot n hthree 0).cosetFDRep ⊞ (simpleRoot n hthree 1).cosetFDRep) ≅
      middleOrbitFDRep ideal half hcard hproper first second) := by
  let := ideal.toRootSubset.dotMulAction hthree
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal first.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal first.vertex)).fintype
  let : Fintype (MulAction.orbit (DihedralGroup n) (spline ideal second.vertex)) :=
    (Finite.finite_mulAction_orbit (spline ideal second.vertex)).fintype
  have hfirstBounds := first.even_bounds hcard hproper
  have hsecondBounds := second.even_bounds hcard hproper
  let firstIndependent := orbit_independent_short ideal first.vertex (simpleRoot n hthree 0)
    (Or.inl rfl) first.ascent hfirstBounds.2.1 first.selected hfirstBounds.2.2
      (first.even_selected hcard hproper)
  let secondIndependent := orbit_independent_short ideal second.vertex (simpleRoot n hthree 1)
    (Or.inr rfl) second.ascent hsecondBounds.2.1 second.selected hsecondBounds.2.2
      (second.even_selected hcard hproper)
  obtain ⟨firstCoset⟩ := high_coset_iso ideal first.vertex (simpleRoot n hthree 0)
    (Or.inl rfl) first.ascent hfirstBounds.2.1 first.selected firstIndependent
  obtain ⟨secondCoset⟩ := high_coset_iso ideal second.vertex (simpleRoot n hthree 1)
    (Or.inr rfl) second.ascent hsecondBounds.2.1 second.selected secondIndependent
  obtain ⟨firstPermutation⟩ := PermutationSpan.iso
    (ideal.toRootSubset.splineRepresentation hthree)
    (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
      (value : ideal.toRootSubset.Spline))
    (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    firstIndependent
  obtain ⟨secondPermutation⟩ := PermutationSpan.iso
    (ideal.toRootSubset.splineRepresentation hthree)
    (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
      (value : ideal.toRootSubset.Spline))
    (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    secondIndependent
  obtain ⟨combined⟩ := PermutationSpan.paired_iso
    (ideal.toRootSubset.splineRepresentation hthree)
    (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
      (value : ideal.toRootSubset.Spline))
    (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
      (value : ideal.toRootSubset.Spline))
    (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    (fun element value => (ideal.toRootSubset.dotMulAction_apply hthree element value.val).symm)
    (middle_orbits_independent ideal half hcard hproper first second)
  exact ⟨biprod.mapIso (firstCoset ≪≫ firstPermutation.symm)
    (secondCoset ≪≫ secondPermutation.symm) ≪≫ combined⟩


/-- The combined middle orbit span lies in its exact homogeneous degree. -/
theorem middle_degree (half : ℕ)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    letI := ideal.toRootSubset.dotMulAction hthree
    Submodule.span ℂ (Set.range (Sum.elim
      (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
        (value : ideal.toRootSubset.Spline))
      (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
        (value : ideal.toRootSubset.Spline)))) ≤ ideal.toRootSubset.piece half := by
  let := ideal.toRootSubset.dotMulAction hthree
  apply Submodule.span_le.mpr
  rintro value ⟨index, rfl⟩
  cases index with
  | inl value =>
    have hmember := orbit_degree ideal first.vertex
      (Submodule.subset_span (show value.val ∈ Set.range
        (fun value : MulAction.orbit (DihedralGroup n) (spline ideal first.vertex) =>
          (value : ideal.toRootSubset.Spline)) from ⟨value, rfl⟩))
    rw [first.degree] at hmember
    exact hmember
  | inr value =>
    have hmember := orbit_degree ideal second.vertex
      (Submodule.subset_span (show value.val ∈ Set.range
        (fun value : MulAction.orbit (DihedralGroup n) (spline ideal second.vertex) =>
          (value : ideal.toRootSubset.Spline)) from ⟨value, rfl⟩))
    rw [second.degree] at hmember
    exact hmember

/-- Inclusion of the combined span intertwines its middle-degree action. -/
def middlePieceMap (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    Representation.IntertwiningMap (middleOrbitFDRep ideal half hcard hproper first second).ρ
      (ideal.toRootSubset.splinePieceRepresentation hthree half) := by
  let := ideal.toRootSubset.dotMulAction hthree
  exact
    { toLinearMap :=
        { toFun := fun value => ⟨value.val, middle_degree ideal half first second value.property⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => by
        apply LinearMap.ext
        intro value
        rfl }

/-- The combined span includes injectively in the middle spline piece. -/
theorem middlePieceMap_injective (half : ℕ) (hcard : ideal.carrier.ncard = 2 * half)
    (hproper : ideal.carrier ≠ positiveRoots n)
    (first : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 0) (n - half))
    (second : HessenbergIdeal.MiddleWitness ideal half (simpleRoot n hthree 1) (n - half)) :
    Function.Injective (middlePieceMap ideal half hcard hproper first second) := by
  intro firstValue secondValue hequal
  apply Subtype.ext
  exact congrArg (fun value : ideal.toRootSubset.piece half => value.val) hequal

end Schubert.DihedralSplines.FlowupSpline
