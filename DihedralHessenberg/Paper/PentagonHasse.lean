import DihedralHessenberg.Paper.PentagonOrientation
import DihedralHessenberg.Paper.OrientedCovers
import DihedralHessenberg.Dihedral.RootAlternatingLength

/-! # Covers in the selected pentagon graph -/

namespace Schubert.DihedralSplines

open Schubert.Dihedral

private theorem pentagon_long_not_cover (selected : RootSubset 5)
    (hcarrier : selected.carrier =
      {(positiveRootEquiv 5 ⟨0, by decide⟩).val,
        (positiveRootEquiv 5 ⟨1, by decide⟩).val,
        (positiveRootEquiv 5 ⟨2, by decide⟩).val}) :
    let a := (simpleRoot 5 (by decide) 0).reflection
    let b := (simpleRoot 5 (by decide) 1).reflection
    ¬@CovBy _ (selected.partialOrder (by decide)).toLT 1 (a * b * a) ∧
    ¬@CovBy _ (selected.partialOrder (by decide)).toLT (a * b) (a * b * a * b * a) ∧
    ¬@CovBy _ (selected.partialOrder (by decide)).toLT b (b * a * b * a) := by
  let a := (simpleRoot 5 (by decide) 0).reflection
  let b := (simpleRoot 5 (by decide) 1).reflection
  have hgraph := pentagon_oriented selected hcarrier
  change selected.orientedEdges (by decide) = _ at hgraph
  have h01 : (1, a) ∈ selected.orientedEdges (by decide) := by rw [hgraph]; simp [a]
  have h12 : (a, a * b) ∈ selected.orientedEdges (by decide) := by rw [hgraph]; simp [a, b]
  have h23 : (a * b, a * b * a) ∈ selected.orientedEdges (by decide) := by
    rw [hgraph]; simp [a, b]
  have h34 : (a * b * a, a * b * a * b) ∈ selected.orientedEdges (by decide) := by
    rw [hgraph]; simp [a, b]
  have h45 : (a * b * a * b, a * b * a * b * a) ∈ selected.orientedEdges (by decide) := by
    rw [hgraph]; simp [a, b]
  have hg12 : (b, b * a) ∈ selected.orientedEdges (by decide) := by rw [hgraph]; simp [a, b]
  have hg23 : (b * a, b * a * b) ∈ selected.orientedEdges (by decide) := by
    rw [hgraph]; simp [a, b]
  have hg34 : (b * a * b, b * a * b * a) ∈ selected.orientedEdges (by decide) := by
    rw [hgraph]; simp [a, b]
  refine ⟨?_, ?_, ?_⟩
  · intro hcover
    exact hcover.2 ((selected.partialOrder_lt (by decide) 1 a).mpr (.single h01))
      ((selected.partialOrder_lt (by decide) a (a * b * a)).mpr
        (.tail (.single h12) h23))
  · intro hcover
    exact hcover.2 ((selected.partialOrder_lt (by decide) (a * b) (a * b * a)).mpr
      (.single h23))
      ((selected.partialOrder_lt (by decide) (a * b * a) (a * b * a * b * a)).mpr
        (.tail (.single h34) h45))
  · intro hcover
    exact hcover.2 ((selected.partialOrder_lt (by decide) b (b * a)).mpr (.single hg12))
      ((selected.partialOrder_lt (by decide) (b * a) (b * a * b * a)).mpr
        (.tail (.single hg23) hg34))

private theorem pentagon_lengths :
    let a := (simpleRoot 5 (by decide) 0).reflection
    let b := (simpleRoot 5 (by decide) 1).reflection
    length 5 (by decide) 1 = 0 ∧ length 5 (by decide) a = 1 ∧
    length 5 (by decide) b = 1 ∧ length 5 (by decide) (a * b) = 2 ∧
    length 5 (by decide) (b * a) = 2 ∧ length 5 (by decide) (a * b * a) = 3 ∧
    length 5 (by decide) (b * a * b) = 3 ∧ length 5 (by decide) (a * b * a * b) = 4 ∧
    length 5 (by decide) (b * a * b * a) = 4 ∧
    length 5 (by decide) (a * b * a * b * a) = 5 := by
  have hfirst (size : ℕ) (hbound : size ≤ 5) := PositiveRoot.alternating_length
    (simpleRoot 5 (by decide) 0) (simpleRoot 5 (by decide) 1) (Or.inl ⟨rfl, rfl⟩) size hbound
  have hsecond (size : ℕ) (hbound : size ≤ 5) := PositiveRoot.alternating_length
    (simpleRoot 5 (by decide) 1) (simpleRoot 5 (by decide) 0) (Or.inr ⟨rfl, rfl⟩) size hbound
  have h0 : length 5 (by decide) 1 = 0 :=
    (coxeterSystem 5 (by decide)).length_eq_zero_iff.mpr rfl
  have h1 := hfirst 1 (by decide)
  have h2 := hsecond 1 (by decide)
  have h3 := hfirst 2 (by decide)
  have h4 := hsecond 2 (by decide)
  have h5 := hfirst 3 (by decide)
  have h6 := hsecond 3 (by decide)
  have h7 := hfirst 4 (by decide)
  have h8 := hsecond 4 (by decide)
  have h9 := hfirst 5 (by decide)
  simp only [PositiveRoot.alternating_succ, PositiveRoot.alternating_zero, mul_one]
    at h1 h2 h3 h4 h5 h6 h7 h8 h9
  simpa only [mul_assoc] using ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- In the three-root pentagon graph, covers are exactly oriented length-one steps. -/
theorem pentagon_cover_iff (selected : RootSubset 5)
    (hcarrier : selected.carrier =
      {(positiveRootEquiv 5 ⟨0, by decide⟩).val,
        (positiveRootEquiv 5 ⟨1, by decide⟩).val,
        (positiveRootEquiv 5 ⟨2, by decide⟩).val})
    (source target : DihedralGroup 5) :
    @CovBy _ (selected.partialOrder (by decide)).toLT source target ↔
      (source, target) ∈ selected.orientedEdges (by decide) ∧
        length 5 (by decide) target = length 5 (by decide) source + 1 := by
  constructor
  · intro hcover
    have hedge := selected.covBy_edge (by decide) source target hcover
    refine ⟨hedge, ?_⟩
    rw [pentagon_oriented selected hcarrier] at hedge
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hedge
    have hnot := pentagon_long_not_cover selected hcarrier
    have hvalues := pentagon_lengths
    rcases hvalues with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    rcases hedge with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals
      first
      | exact False.elim (hnot.1 hcover)
      | exact False.elim (hnot.2.1 hcover)
      | exact False.elim (hnot.2.2 hcover)
      | omega
  · rintro ⟨hedge, hlength⟩
    exact selected.covBy_of_length_succ (by decide) source target hedge hlength

/-- The reachability Hasse graph consists of the twelve stated word endpoint pairs. -/
theorem pentagon_hasse (selected : RootSubset 5)
    (hcarrier : selected.carrier =
      {(positiveRootEquiv 5 ⟨0, by decide⟩).val,
        (positiveRootEquiv 5 ⟨1, by decide⟩).val,
        (positiveRootEquiv 5 ⟨2, by decide⟩).val}) :
    let a := (simpleRoot 5 (by decide) 0).reflection
    let b := (simpleRoot 5 (by decide) 1).reflection
    {pair : DihedralGroup 5 × DihedralGroup 5 |
      @CovBy _ (selected.partialOrder (by decide)).toLT pair.1 pair.2} =
      {(1, a), (1, b), (a, a * b), (a, b * a), (a * b, a * b * a),
        (a * b * a, a * b * a * b), (a * b * a * b, a * b * a * b * a),
        (b * a * b * a, a * b * a * b * a),
        (b * a * b, b * a * b * a), (b * a * b, a * b * a * b),
        (b * a, b * a * b), (b, b * a)} := by
  dsimp only
  have hvalues := pentagon_lengths
  rcases hvalues with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  ext ⟨source, target⟩
  change @CovBy _ (selected.partialOrder (by decide)).toLT source target ↔ _
  rw [pentagon_cover_iff selected hcarrier, pentagon_oriented selected hcarrier]
  constructor
  · rintro ⟨hstep, hlength⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hstep
    rcases hstep with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals first | omega | simp
  · intro hstep
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hstep
    rcases hstep with h | h | h | h | h | h | h | h | h | h | h | h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals constructor
    all_goals first | omega | simp

end Schubert.DihedralSplines
