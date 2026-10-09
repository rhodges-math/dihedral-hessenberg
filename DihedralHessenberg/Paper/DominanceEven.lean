import DihedralHessenberg.Paper.HessenbergEvenEdges
import DihedralHessenberg.Dihedral.RootAlternatingLength
import DihedralHessenberg.Paper.HessenbergVectorDominant

/-! # Dominant simple vectors for proper even-cardinality ideals -/

namespace Schubert.DihedralSplines.HessenbergIdeal

open Schubert.Dihedral

variable {n : ℕ} {hthree : 3 ≤ n}

/-- A proper ideal contains fewer than n positive vectors. -/
theorem card_lt (ideal : HessenbergIdeal n hthree)
    (hproper : ideal.carrier ≠ positiveRoots n) : ideal.carrier.ncard < n := by
  have hbound := ideal.indexed.card_le
  by_contra hnot
  have hcard : ideal.indexed.roots.card = n := by
    rw [← ideal.ncard_indexed] at hbound ⊢
    omega
  have hfull : ideal.indexed.roots = Finset.univ :=
    Finset.eq_univ_of_card ideal.indexed.roots (by simpa only [Fintype.card_fin] using hcard)
  apply hproper
  ext vector
  constructor
  · exact fun hmem => ideal.positive hmem
  · intro hpositive
    obtain ⟨index, rfl⟩ := hpositive
    apply (ideal.mem_indexed index).mp
    rw [hfull]
    exact Finset.mem_univ index

/-- Every simple vector is dominant for a proper ideal of even root cardinality. -/
theorem dominant_even (ideal : HessenbergIdeal n hthree) (half : ℕ)
    (hcard : ideal.carrier.ncard = 2 * half) (hproper : ideal.carrier ≠ positiveRoots n)
    (alpha : PositiveRoot n)
    (hsimple : alpha = simpleRoot n hthree 0 ∨ alpha = simpleRoot n hthree 1) :
    ideal.IsDominant alpha := by
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
  refine ⟨beta, hpair, n - half, by omega, by omega, ?_⟩
  dsimp only
  change ideal.toRootSubset.length element = ideal.carrier.ncard / 2 ∧
    (element, alpha.reflection * element) ∈ ideal.toRootSubset.edges ∧
      (element, beta.reflection * element) ∉ ideal.toRootSubset.edges
  rw [hcard]
  exact ⟨by omega, hedge, hnot⟩

end Schubert.DihedralSplines.HessenbergIdeal
