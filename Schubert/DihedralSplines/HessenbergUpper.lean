import Schubert.DihedralSplines.SelectedUpper
import Schubert.DihedralSplines.AscendingNeighbors
import Schubert.DihedralSplines.RootFullDegree
import Schubert.Dihedral.RootReflectionLengthVectors
import Schubert.DihedralSplines.HessenbergVectorDegree
import Schubert.DihedralSplines.HessenbergLengthRanges

/-! # Selected regular upper ideals -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A minimum with sufficient selected reflections and complementary inversion degree. -/
structure Upper (ideal : HessenbergIdeal n hthree) where
  /-- The minimum of the Bruhat upper ideal. -/
  minimum : DihedralGroup n
  /-- Selected reflections reach the last possible internal length. -/
  bound : 2 * (n - length n hthree minimum) - 1 ≤ ideal.carrier.ncard
  /-- The selected degree is complementary to the full internal degree. -/
  degree : ideal.toRootSubset.length minimum =
    ideal.carrier.ncard - (n - length n hthree minimum)

namespace Upper

variable {ideal : HessenbergIdeal n hthree}

private theorem ascent_conditions (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1)
    (hhalf : n < 2 * length n hthree element + 1)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges) :
    2 * (n - length n hthree element) - 1 ≤ ideal.carrier.ncard ∧
      ideal.toRootSubset.length element = ideal.carrier.ncard - (n - length n hthree element) := by
  have hup := bruhatLE_of_length_lt n hthree (show length n hthree element <
    length n hthree (alpha.reflection * element) by omega)
  have hne : element ≠ alpha.reflection * element := by
    intro heq
    have := congrArg (length n hthree) heq
    omega
  obtain ⟨gamma, hselected, hneighbor⟩ := (ideal.toRootSubset.mem_edges _).mp hedge
  have hreflection := alpha.ascent_length hthree gamma hsimple element hup hne hneighbor
  rw [ite_eq_right (by omega)] at hreflection
  have hbound := ideal.reflection_length_le gamma hselected
  rw [hreflection] at hbound
  have hnextBound := length_le_polygon_parameter n hthree (alpha.reflection * element)
  have hupper : n - ideal.carrier.ncard / 2 ≤
      length n hthree (alpha.reflection * element) := by omega
  have hhalfCard : 2 * (ideal.carrier.ncard / 2) ≤ ideal.indexed.roots.card := by
    rw [← ideal.ncard_indexed]
    omega
  have hnextDegree : ideal.toRootSubset.length (alpha.reflection * element) =
      ideal.carrier.ncard - (n - length n hthree (alpha.reflection * element)) := by
    rw [ideal.length_indexed, ideal.ncard_indexed]
    exact HessenbergSpace.LengthRanges.card_sub_complementary ideal.indexed
      (ideal.carrier.ncard / 2) hhalfCard _ hupper
  have hstep := ideal.length_edge alpha hsimple element hup hne hedge
  rw [hnextDegree] at hstep
  exact ⟨hbound, by omega⟩

/-- A selected upper-half simple ascent gives a regular upper ideal at its vertex. -/
def ofAscent (ideal : HessenbergIdeal n hthree) (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1)
    (element : DihedralGroup n)
    (hascent : length n hthree (alpha.reflection * element) = length n hthree element + 1)
    (hhalf : n < 2 * length n hthree element + 1)
    (hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges) : Upper ideal where
  minimum := element
  bound := (ascent_conditions ideal alpha hsimple element hascent hhalf hedge).1
  degree := (ascent_conditions ideal alpha hsimple element hascent hhalf hedge).2

private theorem full_card : (RootSubset.full n).carrier.ncard = n := by
  change (Set.range (positiveRoot n)).ncard = n
  rw [Set.ncard_range_of_injective (positiveRoot_injective n), Nat.card_fin]

/-- The ascending star at the minimum contains every full-root edge. -/
theorem star_full (upper : Upper ideal) (target : DihedralGroup n)
    (hup : BruhatLE n hthree upper.minimum target) :
    (upper.minimum, target) ∈ ideal.toRootSubset.edges ↔
      (upper.minimum, target) ∈ (RootSubset.full n).edges := by
  classical
  let : NeZero n := ⟨by omega⟩
  let selected : Set (DihedralGroup n) := {target |
    (upper.minimum, target) ∈ ideal.toRootSubset.edges ∧
      length n hthree upper.minimum < length n hthree target}
  let full : Set (DihedralGroup n) := {target |
    (upper.minimum, target) ∈ (RootSubset.full n).edges ∧
      length n hthree upper.minimum < length n hthree target}
  have hsubset : selected ⊆ full := by
    intro vertex hvertex
    obtain ⟨alpha, _, hneighbor⟩ := (ideal.toRootSubset.mem_edges _).mp hvertex.1
    exact ⟨⟨alpha, alpha.property, hneighbor⟩, hvertex.2⟩
  have hcard : full.ncard ≤ selected.ncard := by
    change {target | (upper.minimum, target) ∈ (RootSubset.full n).edges ∧
      length n hthree upper.minimum < length n hthree target}.ncard ≤ _
    rw [RootSubset.ascending_card, full_card, RootSubset.length_full n hthree]
    change _ ≤ {target | (upper.minimum, target) ∈ ideal.toRootSubset.edges ∧
      length n hthree upper.minimum < length n hthree target}.ncard
    rw [RootSubset.ascending_card, upper.degree]
    have hbound := upper.bound
    omega
  have heq : selected = full := Set.eq_of_subset_of_ncard_le hsubset hcard
  constructor
  · intro hedge
    obtain ⟨alpha, _, hneighbor⟩ := (ideal.toRootSubset.mem_edges _).mp hedge
    exact ⟨alpha, alpha.property, hneighbor⟩
  · intro hedge
    have hne := (RootSubset.full n).edge_lengths_ne hthree upper.minimum target hedge
    have hstrict : length n hthree upper.minimum < length n hthree target := by
      have hlength := bruhatLE_length_le n hthree hup
      omega
    have hmem : target ∈ full := ⟨hedge, hstrict⟩
    have hselected : target ∈ selected := heq.symm ▸ hmem
    exact hselected.1

/-- The entire induced upper graph equals its full-root endpoint graph. -/
theorem internal_full (upper : Upper ideal) (source target : DihedralGroup n)
    (hsource : BruhatLE n hthree upper.minimum source)
    (htarget : BruhatLE n hthree upper.minimum target) :
    (source, target) ∈ ideal.toRootSubset.edges ↔
      (source, target) ∈ (RootSubset.full n).edges := by
  constructor
  · intro hedge
    obtain ⟨alpha, _, hneighbor⟩ := (ideal.toRootSubset.mem_edges _).mp hedge
    exact ⟨alpha, alpha.property, hneighbor⟩
  · intro hedge
    by_cases hfirst : source = upper.minimum
    · subst source
      exact (upper.star_full target htarget).mpr hedge
    by_cases hsecond : target = upper.minimum
    · subst target
      exact ideal.toRootSubset.edge_symm
        ((upper.star_full source hsource).mpr ((RootSubset.full n).edge_symm hedge))
    have hfirstLength : length n hthree upper.minimum < length n hthree source :=
      ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp hsource).resolve_left (Ne.symm hfirst)
    have hsecondLength : length n hthree upper.minimum < length n hthree target :=
      ((bruhatLE_iff_eq_or_length_lt n hthree _ _).mp htarget).resolve_left (Ne.symm hsecond)
    have hbound := upper.bound
    have hne := (RootSubset.full n).edge_lengths_ne hthree source target hedge
    have hsourceBound := length_le_polygon_parameter n hthree source
    have htargetBound := length_le_polygon_parameter n hthree target
    by_cases hless : length n hthree source < length n hthree target
    · exact (ideal.internal_full source (by omega) source target
        (bruhatLE_refl n hthree source) (bruhatLE_of_length_lt n hthree hless)).mpr hedge
    · exact (ideal.internal_full target (by omega) source target
        (bruhatLE_of_length_lt n hthree (by omega))
        (bruhatLE_refl n hthree target)).mpr hedge

/-- Functions invariant on internal selected edges are constant throughout the upper ideal. -/
theorem eq_of_edges (upper : Upper ideal) {A : Sort*} (value : DihedralGroup n → A)
    (hinvariant : ∀ source target, BruhatLE n hthree upper.minimum source →
      BruhatLE n hthree upper.minimum target → (source, target) ∈ ideal.toRootSubset.edges →
        value source = value target) :
    ∀ vertex, BruhatLE n hthree upper.minimum vertex → value vertex = value upper.minimum := by
  apply RootSubset.eq_on_upper n hthree upper.minimum value
  intro source target hsource htarget hedge
  exact hinvariant source target hsource htarget
    ((upper.internal_full source target hsource htarget).mpr hedge)

/-- Every vertex of the selected upper ideal has its minimum's inversion boundary degree. -/
theorem boundary_card (upper : Upper ideal) (source : DihedralGroup n)
    (hsource : BruhatLE n hthree upper.minimum source) :
    {target : DihedralGroup n | (source, target) ∈ ideal.toRootSubset.edges ∧
      ¬BruhatLE n hthree upper.minimum target}.ncard =
        ideal.toRootSubset.length upper.minimum := by
  classical
  let : NeZero n := ⟨by omega⟩
  let vertices : Set (DihedralGroup n) := {target | BruhatLE n hthree upper.minimum target}
  let selected : Set (DihedralGroup n) := {target | (source, target) ∈ ideal.toRootSubset.edges}
  let full : Set (DihedralGroup n) := {target | (source, target) ∈ (RootSubset.full n).edges}
  have hinter : selected ∩ vertices = full ∩ vertices := by
    ext target
    constructor
    · rintro ⟨hedge, htarget⟩
      exact ⟨(upper.internal_full source target hsource htarget).mp hedge, htarget⟩
    · rintro ⟨hedge, htarget⟩
      exact ⟨(upper.internal_full source target hsource htarget).mpr hedge, htarget⟩
  have hfull := Set.ncard_inter_add_ncard_sdiff_eq_ncard full vertices
  have hselected := Set.ncard_inter_add_ncard_sdiff_eq_ncard selected vertices
  have hfullBoundary : (full \ vertices).ncard = length n hthree upper.minimum :=
    RootSubset.ncard_upper_boundary n hthree upper.minimum source hsource
  have hfullTotal : full.ncard = n := by
    exact ((RootSubset.full n).neighbor_card source).trans full_card
  have hselectedTotal : selected.ncard = ideal.carrier.ncard :=
    ideal.toRootSubset.neighbor_card source
  rw [hfullBoundary, hfullTotal] at hfull
  rw [hinter, hselectedTotal] at hselected
  change (selected \ vertices).ncard = ideal.toRootSubset.length upper.minimum
  rw [upper.degree]
  have hbound := length_le_polygon_parameter n hthree upper.minimum
  omega

end Upper

end Schubert.DihedralSplines.HessenbergIdeal
