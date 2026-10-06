import Schubert.DihedralSplines.DominanceOdd

/-! # High alternating witnesses for middle-degree dominance -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- An alternating middle-degree vertex with its selected ascending and absent descending edge. -/
structure MiddleWitness (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (alpha : PositiveRoot n) (size : ℕ) where
  /-- The other simple vector. -/
  beta : PositiveRoot n
  /-- The two simple vectors in their specified order. -/
  pair : (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
    (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0)
  /-- The group vertex. -/
  vertex : DihedralGroup n
  /-- Its alternating expression. -/
  word : vertex = beta.alternatingProduct alpha size
  /-- Its canonical Coxeter length. -/
  canonical : length n hthree vertex = size
  /-- Its middle Hessenberg degree. -/
  degree : ideal.toRootSubset.length vertex = half
  /-- Left multiplication by the prescribed simple reflection is an ascent. -/
  ascent : length n hthree (alpha.reflection * vertex) = length n hthree vertex + 1
  /-- The ascending endpoint pair is selected. -/
  selected : (vertex, alpha.reflection * vertex) ∈ ideal.toRootSubset.edges
  /-- The other simple endpoint pair is absent. -/
  absent : (vertex, beta.reflection * vertex) ∉ ideal.toRootSubset.edges

/-- Each prescribed simple vector has a high middle witness for a proper even ideal. -/
theorem middle_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    Nonempty (MiddleWitness ideal half alpha (n - half)) := by
  have hmaximum := card_lt ideal hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  obtain ⟨beta, hpair⟩ : ∃ beta : PositiveRoot n,
      (alpha = simpleRoot n hthree 0 ∧ beta = simpleRoot n hthree 1) ∨
        (alpha = simpleRoot n hthree 1 ∧ beta = simpleRoot n hthree 0) := by
    rcases hsimple with hfirst | hsecond
    · exact ⟨simpleRoot n hthree 1, Or.inl ⟨hfirst, rfl⟩⟩
    · exact ⟨simpleRoot n hthree 0, Or.inr ⟨hsecond, rfl⟩⟩
  have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
    rcases hpair with hfirst | hsecond
    · exact Or.inr ⟨hfirst.2, hfirst.1⟩
    · exact Or.inl ⟨hsecond.2, hsecond.1⟩
  have hbetaSimple : beta = simpleRoot n hthree 0 ∨ beta = simpleRoot n hthree 1 := by
    rcases hpair with hfirst | hsecond
    · exact Or.inr hfirst.2
    · exact Or.inl hsecond.2
  let element := beta.alternatingProduct alpha (n - half)
  have hlength : length n hthree element = n - half :=
    PositiveRoot.alternating_length beta alpha hreverse _ (by omega)
  have hascent : length n hthree (alpha.reflection * element) =
      length n hthree element + 1 := by
    rw [hlength]
    exact PositiveRoot.alternating_ascent alpha beta hpair _ (by omega)
  have hdescent : length n hthree (beta.reflection * element) + 1 =
      length n hthree element := by
    rw [hlength]
    exact PositiveRoot.alternating_descent alpha beta hpair _ (by omega) (by omega)
  have hedge : (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges := by
    rw [ideal.edge_ascent_even half hcard alpha hsimple element hascent, hlength]
    exact Or.inr le_rfl
  have hnot : (element, beta.reflection * element) ∉ ideal.toRootSubset.edges := by
    rw [ideal.edge_descent_even half hcard beta hbetaSimple element hdescent, hlength]
    omega
  have hdegree : ideal.toRootSubset.length element = half := by
    rw [ideal.length_even half hcard element, hlength, hcard]
    split_ifs <;> omega
  exact ⟨⟨beta, hpair, element, rfl, hlength, hdegree, hascent, hedge, hnot⟩⟩

/-- A dominant simple vector has the precise high witness for a proper odd ideal. -/
theorem middle_odd (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha : PositiveRoot n) (hdominant : ideal.IsDominant alpha) :
    Nonempty (MiddleWitness ideal half alpha (n - half - 1)) := by
  obtain ⟨beta, hpair, hdegree, hedge, hnot⟩ :=
    ideal.dominant_odd_witness half hcard hproper alpha hdominant
  have hmaximum := ideal.card_lt hproper
  have hminimum := ideal.indexed.two_le_card
  rw [← ideal.ncard_indexed, hcard] at hminimum
  rw [hcard] at hmaximum
  have hreverse : (beta = simpleRoot n hthree 0 ∧ alpha = simpleRoot n hthree 1) ∨
      (beta = simpleRoot n hthree 1 ∧ alpha = simpleRoot n hthree 0) := by
    rcases hpair with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  let element := beta.alternatingProduct alpha (n - half - 1)
  have hlength : length n hthree element = n - half - 1 :=
    PositiveRoot.alternating_length beta alpha hreverse _ (by omega)
  have hascent : length n hthree (alpha.reflection * element) =
      length n hthree element + 1 := by
    rw [hlength]
    exact PositiveRoot.alternating_ascent alpha beta hpair _ (by omega)
  have hmiddle : ideal.toRootSubset.length element = half := by
    change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 at hdegree
    rw [hcard] at hdegree
    omega
  exact ⟨⟨beta, hpair, element, rfl, hlength, hmiddle, hascent, hedge, hnot⟩⟩

/-- A proper odd ideal has a simple vector carrying its high middle witness. -/
theorem middle_odd_exists (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half + 1) (hproper : ideal.carrier ≠ positiveRoots n) :
    ∃ alpha : PositiveRoot n,
      (alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) ∧
        Nonempty (MiddleWitness ideal half alpha (n - half - 1)) := by
  obtain ⟨alpha, ⟨hsimple, hdominant⟩, _⟩ := ideal.dominant_odd_unique half hcard hproper
  exact ⟨alpha, hsimple, ideal.middle_odd half hcard hproper alpha hdominant⟩

end Schubert.DihedralSplines.HessenbergIdeal
